/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Counting and evaluating perfect pairings of finite label sets. -/

/-
proof_shape: perfectPairingEquiv: content (private bridge).
proof_shape: partialPairingCount: content (consumer:
  TopOrderObstructionFamily.mixture_propagation_limit).
proof_shape: pairingSupport_card, IsPerfectPairing.card: bind-only
  (consumers: finitePairingPolynomial_const, perfectPairingCount,
    SixthOrderTopPairingRefutation).
proof_shape: finitePairingPolynomial_rankOne, finitePairingPolynomial_const,
  perfectPairingCount: bind-only (consumer: SixthOrderTopPairingRefutation).
escape_witness: A perfect pairing is identified with the fixed-point-free
  involution exchanging each edge's endpoints. The bridge reuses the existing
  cycle-type count rather than proving a second counting recursion.
  partialPairingCount identifies the support fibers with perfect pairings and
  proves the count choose(U.card, 2*p) * (2*p-1)!! for partial pairings.
admission_basis: escape-witness.
-/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PartialPairingPolynomial
import D5.S3.Zeros.Convolution.PerfectMatchingCount

/-! Cardinality and evaluations of finite perfect pairings. -/

open scoped BigOperators
namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Disjoint two-element edges cover exactly twice their number of labels. -/
private theorem pairingSupport_card {U : Finset α} {P : Finset (Finset α)}
    (hP : IsPartialPairing U P) : (pairingSupport P).card = 2 * P.card := by
  change (P.biUnion fun e => e).card = 2 * P.card
  rw [Finset.card_biUnion hP.2.1]
  rw [Finset.sum_congr rfl hP.1]
  simp [Nat.mul_comm]

/-- A perfect pairing has half as many edges as covered labels. -/
theorem IsPerfectPairing.card {U : Finset α} {P : Finset (Finset α)}
    (hP : IsPerfectPairing U P) : U.card = 2 * P.card := by
  rw [← hP.2]
  exact pairingSupport_card hP.1

/-- Rank-one edge weights have the same product on every perfect pairing. -/
theorem finitePairingPolynomial_rankOne (U : Finset α) (c : Finset α → ℝ)
    (x : α → ℝ) (hc : ∀ e, e.card = 2 → c e = ∏ i ∈ e, x i) :
    finitePairingPolynomial U c =
      (((Finset.univ : Finset (Finset (Finset α))).filter
        (IsPerfectPairing U)).card : ℝ) * ∏ i ∈ U, x i := by
  unfold finitePairingPolynomial
  have hprod (P : Finset (Finset α)) (hP : IsPerfectPairing U P) :
      (∏ e ∈ P, c e) = ∏ i ∈ U, x i := by
    rw [Finset.prod_congr rfl (fun e he => hc e (hP.1.1 e he))]
    have h := Finset.prod_biUnion (f := x) hP.1.2.1
    change (∏ i ∈ pairingSupport P, x i) = ∏ e ∈ P, ∏ i ∈ e, x i at h
    rw [hP.2] at h
    exact h.symm
  rw [Finset.sum_congr rfl (fun P hP => hprod P (Finset.mem_filter.mp hP).2)]
  simp

/-- Constant edge weights contribute one power per edge of a perfect pairing. -/
theorem finitePairingPolynomial_const (U : Finset α) (c : Finset α → ℝ)
    (κ : ℝ) (hc : ∀ e, e.card = 2 → c e = κ) :
    finitePairingPolynomial U c =
      (((Finset.univ : Finset (Finset (Finset α))).filter
        (IsPerfectPairing U)).card : ℝ) * κ ^ (U.card / 2) := by
  unfold finitePairingPolynomial
  have hprod (P : Finset (Finset α)) (hP : IsPerfectPairing U P) :
      (∏ e ∈ P, c e) = κ ^ (U.card / 2) := by
    rw [Finset.prod_congr rfl (fun e he => hc e (hP.1.1 e he))]
    have hcard : P.card = U.card / 2 := by rw [hP.card]; omega
    simp [hcard]
  rw [Finset.sum_congr rfl (fun P hP => hprod P (Finset.mem_filter.mp hP).2)]
  simp

private theorem pairing_partner_exists (U : Finset α) (P : Finset (Finset α))
    (hP : IsPerfectPairing U P) (a : U) :
    ∃ b : U, b ≠ a ∧ {a.val, b.val} ∈ P := by
  obtain ⟨e, he, hae⟩ := (mem_pairingSupport a.val P).mp (hP.2.symm ▸ a.property)
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp (hP.1.1 e he)
  have hx : x ∈ U := hP.1.2.2 ((mem_pairingSupport x P).2 ⟨{x, y}, he, by simp⟩)
  have hy : y ∈ U := hP.1.2.2 ((mem_pairingSupport y P).2 ⟨{x, y}, he, by simp⟩)
  rcases (show a.val = x ∨ a.val = y by simpa using hae) with ha | ha
  · refine ⟨⟨y, hy⟩, ?_, ?_⟩
    · intro h; exact hxy (ha.symm.trans (congrArg Subtype.val h).symm)
    · simpa [ha] using he
  · refine ⟨⟨x, hx⟩, ?_, ?_⟩
    · intro h; exact hxy ((congrArg Subtype.val h).trans ha)
    · simpa [ha, Finset.pair_comm] using he

private theorem pairing_partner_unique {U : Finset α} {P : Finset (Finset α)}
    (hP : IsPerfectPairing U P) {a b c : U}
    (hb : b ≠ a ∧ {a.val, b.val} ∈ P)
    (hc : c ≠ a ∧ {a.val, c.val} ∈ P) : b = c := by
  have he : ({a.val, b.val} : Finset α) = {a.val, c.val} := by
    by_contra hn
    exact Finset.disjoint_left.mp (hP.1.2.1 hb.2 hc.2 hn)
      (show a.val ∈ ({a.val, b.val} : Finset α) by simp) (by simp)
  apply Subtype.ext
  have hm : b.val ∈ ({a.val, c.val} : Finset α) := he ▸ (by simp)
  rcases Finset.mem_insert.mp hm with h | h
  · exact False.elim (hb.1 (Subtype.ext h))
  · exact Finset.mem_singleton.mp h

private def pairingPartner (U : Finset α) (P : Finset (Finset α))
    (hP : IsPerfectPairing U P) (a : U) : U :=
  Classical.choose (pairing_partner_exists U P hP a)

private theorem pairingPartner_spec (U : Finset α) (P : Finset (Finset α))
    (hP : IsPerfectPairing U P) (a : U) :
    pairingPartner U P hP a ≠ a ∧ {a.val, (pairingPartner U P hP a).val} ∈ P :=
  Classical.choose_spec (pairing_partner_exists U P hP a)

private def pairingInvolution (U : Finset α) (P : Finset (Finset α))
    (hP : IsPerfectPairing U P) :
    D5.S3.Zeros.Convolution.PerfectMatchingCount.FixedPointFreeInvolution U := by
  let f := pairingPartner U P hP
  have hf (a : U) : f (f a) = a := by
    apply pairing_partner_unique hP (pairingPartner_spec U P hP (f a))
    exact ⟨(pairingPartner_spec U P hP a).1.symm,
      by simpa only [Finset.pair_comm] using (pairingPartner_spec U P hP a).2⟩
  exact ⟨⟨f, f, hf, hf⟩, hf, fun a => (pairingPartner_spec U P hP a).1⟩

private def involutionPairing (U : Finset α)
    (p : D5.S3.Zeros.Convolution.PerfectMatchingCount.FixedPointFreeInvolution U) :
    Finset (Finset α) := Finset.univ.image fun a : U => {a.val, (p.val a).val}

private theorem involutionPairing_valid (U : Finset α)
    (p : D5.S3.Zeros.Convolution.PerfectMatchingCount.FixedPointFreeInvolution U) :
    IsPerfectPairing U (involutionPairing U p) := by
  have hne (a : U) : a.val ≠ (p.val a).val := by
    intro h; exact p.property.2 a (Subtype.ext h.symm)
  have hed (a b : U) (h : a.val = b.val ∨ a.val = (p.val b).val ∨
      (p.val a).val = b.val ∨ (p.val a).val = (p.val b).val) :
      ({a.val, (p.val a).val} : Finset α) = {b.val, (p.val b).val} := by
    rcases h with h | h | h | h
    · have hab : a = b := Subtype.ext h
      rw [hab]
    · have hab : a = p.val b := Subtype.ext h
      simp [hab, p.property.1 b, Finset.pair_comm]
    · have hab : b = p.val a := Subtype.ext h.symm
      simp [hab, p.property.1 a, Finset.pair_comm]
    · have hab := p.val.injective (Subtype.ext h)
      rw [hab]
  have hs : pairingSupport (involutionPairing U p) = U := by
    ext a
    simp only [mem_pairingSupport, involutionPairing, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨e, ⟨x, rfl⟩, ha⟩
      rcases (show a = x.val ∨ a = (p.val x).val by simpa using ha) with rfl | rfl
      · exact x.property
      · exact (p.val x).property
    · intro ha
      exact ⟨{a, (p.val ⟨a, ha⟩).val}, ⟨⟨a, ha⟩, rfl⟩, by simp⟩
  refine ⟨⟨?_, ?_, hs.le⟩, hs⟩
  · intro e he
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    simp [hne a]
  · intro e he d hd hED
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hd
    apply Finset.disjoint_left.mpr
    intro x hx hy
    apply hED
    apply hed a b
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

/-- A perfect pairing is equivalently the fixed-point-free involution exchanging
its two endpoints in every edge. -/
private def perfectPairingEquiv (U : Finset α) :
    {P : Finset (Finset α) // IsPerfectPairing U P} ≃
      D5.S3.Zeros.Convolution.PerfectMatchingCount.FixedPointFreeInvolution U where
  toFun P := pairingInvolution U P.val P.property
  invFun p := ⟨involutionPairing U p, involutionPairing_valid U p⟩
  left_inv P := by
    apply Subtype.ext
    apply Finset.ext
    intro e
    constructor
    · intro he
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
      exact (pairingPartner_spec U P.val P.property a).2
    · intro he
      obtain ⟨x, y, hxy, heq⟩ := Finset.card_eq_two.mp (P.property.1.1 e he)
      have hx : x ∈ U := P.property.1.2.2 ((mem_pairingSupport x P.val).2
        ⟨e, he, by rw [heq]; simp⟩)
      have hy : y ∈ U := P.property.1.2.2 ((mem_pairingSupport y P.val).2
        ⟨e, he, by rw [heq]; simp⟩)
      have hp : pairingPartner U P.val P.property ⟨x, hx⟩ = ⟨y, hy⟩ := by
        apply pairing_partner_unique P.property (pairingPartner_spec U P.val P.property ⟨x, hx⟩)
        exact ⟨fun h => hxy (congrArg Subtype.val h).symm, heq ▸ he⟩
      apply Finset.mem_image.mpr
      refine ⟨⟨x, hx⟩, Finset.mem_univ _, ?_⟩
      change {x, (pairingPartner U P.val P.property ⟨x, hx⟩).val} = e
      rw [hp]
      exact heq.symm
  right_inv p := by
    apply Subtype.ext
    apply Equiv.ext
    intro a
    change pairingPartner U (involutionPairing U p) (involutionPairing_valid U p) a = p.val a
    apply pairing_partner_unique (involutionPairing_valid U p)
      (pairingPartner_spec U _ (involutionPairing_valid U p) a)
    refine ⟨p.property.2 a, ?_⟩
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩

/-- A set of even cardinality has the usual odd double-factorial number of perfect
pairings; a set of odd cardinality has none. -/
theorem perfectPairingCount (U : Finset α) :
    ((Finset.univ : Finset (Finset (Finset α))).filter
      (IsPerfectPairing U)).card =
      if Even U.card then Nat.doubleFactorial (U.card - 1) else 0 := by
  by_cases hU : Even U.card
  · rw [if_pos hU]
    obtain ⟨m, hm⟩ := hU
    have hcard : U.card = 2 * m := by omega
    have hc : Fintype.card U = 2 * m := by simpa using hcard
    have he := Fintype.card_congr (perfectPairingEquiv U)
    rw [Fintype.card_subtype] at he
    rw [he, D5.S3.Zeros.Convolution.PerfectMatchingCount.card_fixedPointFreeInvolution m hc,
      hcard]
    apply Nat.div_eq_of_eq_mul_right (by positivity)
    cases m with
    | zero => norm_num [Nat.doubleFactorial]
    | succ m =>
      rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
        Nat.factorial_eq_mul_doubleFactorial,
        show 2 * m + 1 + 1 = 2 * (m + 1) by omega,
        Nat.doubleFactorial_two_mul]
      ring
  · rw [if_neg hU]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro P hP hPP
    apply hU
    exact ⟨P.card, by have hh := hPP.card; omega⟩

/-- The support of a partial pairing with `p` edges can be chosen in
`choose U.card (2*p)` ways, after which its edges form a perfect pairing. -/
theorem partialPairingCount (U : Finset α) (p : ℕ) :
    ((Finset.univ : Finset (Finset (Finset α))).filter
      (fun P => IsPartialPairing U P ∧ P.card = p)).card =
      U.card.choose (2 * p) * Nat.doubleFactorial (2 * p - 1) := by
  classical
  let A := (Finset.univ : Finset (Finset (Finset α))).filter
    (fun P => IsPartialPairing U P ∧ P.card = p)
  let B := U.powersetCard (2 * p)
  have hm : (A : Set (Finset (Finset α))).MapsTo pairingSupport B := by
    intro P hPA
    obtain ⟨hP, hp⟩ := (Finset.mem_filter.mp hPA).2
    have hc := (show IsPerfectPairing (pairingSupport P) P from
      ⟨⟨hP.1, hP.2.1, fun _ h => h⟩, rfl⟩).card
    exact Finset.mem_powersetCard.mpr ⟨hP.2.2, by simpa [hp] using hc⟩
  have hf (S : Finset α) (hS : S ∈ B) :
      A.filter (fun P => pairingSupport P = S) =
        (Finset.univ.filter (IsPerfectPairing S) : Finset (Finset (Finset α))) := by
    obtain ⟨hSU, hSc⟩ := Finset.mem_powersetCard.mp hS
    ext P
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hP, _⟩, hs⟩
      exact ⟨⟨hP.1, hP.2.1, hs.le⟩, hs⟩
    · intro hP
      have hp : P.card = p := by have hc := hP.card; omega
      exact ⟨⟨⟨hP.1.1, hP.1.2.1, hP.1.2.2.trans hSU⟩, hp⟩, hP.2⟩
  change A.card = _
  rw [Finset.card_eq_sum_card_fiberwise hm]
  calc
    (∑ S ∈ B, (A.filter (fun P => pairingSupport P = S)).card) =
        ∑ _S ∈ B, Nat.doubleFactorial (2 * p - 1) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [hf S hS, perfectPairingCount,
        (Finset.mem_powersetCard.mp hS).2, if_pos (even_two_mul p)]
    _ = _ := by simp [B]

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

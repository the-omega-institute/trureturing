/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartialPairingPolynomial
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartialPairingPolynomial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Perfect pairing polynomials expand over partial pairings without multiplicities. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.QuadraticMomentDefs

/-! The finite matching decomposition behind arbitrary-order pairing polynomials. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The labels used by a finite collection of edges. -/
def pairingSupport (P : Finset (Finset α)) : Finset α := P.biUnion id

/-- A partial pairing consists of disjoint two-element subsets of the label set. -/
def IsPartialPairing (U : Finset α) (P : Finset (Finset α)) : Prop :=
  (∀ e ∈ P, e.card = 2) ∧ (P : Set (Finset α)).Pairwise Disjoint ∧ pairingSupport P ⊆ U

/-- A perfect pairing covers every label. -/
def IsPerfectPairing (U : Finset α) (P : Finset (Finset α)) : Prop :=
  IsPartialPairing U P ∧ pairingSupport P = U

/-- The arbitrary-order perfect pairing polynomial, including the empty pairing. -/
def finitePairingPolynomial (U : Finset α) (c : Finset α → ℝ) : ℝ :=
  ∑ P : Finset (Finset α) with IsPerfectPairing U P, ∏ e ∈ P, c e

omit [Fintype α] in
private theorem mem_pairingSupport (i : α) (P : Finset (Finset α)) :
    i ∈ pairingSupport P ↔ ∃ e ∈ P, i ∈ e := by
  simp [pairingSupport]

omit [Fintype α] in
private theorem partialPairing_subset {U : Finset α} {P M : Finset (Finset α)}
    (hM : IsPartialPairing U M) (hPM : P ⊆ M) : IsPartialPairing U P := by
  refine ⟨fun e he => hM.1 e (hPM he), hM.2.1.mono hPM, ?_⟩
  intro i hi
  obtain ⟨e, he, hie⟩ := (mem_pairingSupport i P).1 hi
  exact hM.2.2 ((mem_pairingSupport i M).2 ⟨e, hPM he, hie⟩)

omit [Fintype α] in
private theorem pairing_remainder {U : Finset α} {M P : Finset (Finset α)}
    (hM : IsPerfectPairing U M) (hPM : P ⊆ M) :
    IsPartialPairing U P ∧ IsPerfectPairing (U \ pairingSupport P) (M \ P) := by
  have hP := partialPairing_subset hM.1 hPM
  have hQ := partialPairing_subset hM.1 (Finset.sdiff_subset : M \ P ⊆ M)
  have hsub : pairingSupport (M \ P) ⊆ U \ pairingSupport P := by
    intro i hi
    obtain ⟨e, he, hie⟩ := (mem_pairingSupport i (M \ P)).1 hi
    rcases Finset.mem_sdiff.mp he with ⟨heM, heP⟩
    refine Finset.mem_sdiff.mpr ⟨hQ.2.2 hi, ?_⟩
    intro hiP
    obtain ⟨d, hd, hid⟩ := (mem_pairingSupport i P).1 hiP
    have hed : e ≠ d := fun h => heP (h.symm ▸ hd)
    exact Finset.disjoint_left.mp (hM.1.2.1 heM (hPM hd) hed) hie hid
  refine ⟨hP, ⟨hQ.1, hQ.2.1, hsub⟩, Finset.Subset.antisymm hsub ?_⟩
  intro i hi
  rcases Finset.mem_sdiff.mp hi with ⟨hiU, hiP⟩
  have hiM : i ∈ pairingSupport M := hM.2.symm ▸ hiU
  obtain ⟨e, he, hie⟩ := (mem_pairingSupport i M).1 hiM
  exact (mem_pairingSupport i (M \ P)).2
    ⟨e, Finset.mem_sdiff.mpr ⟨he, fun heP => hiP
      ((mem_pairingSupport i P).2 ⟨e, heP, hie⟩)⟩, hie⟩

omit [Fintype α] in
private theorem pairing_join {U : Finset α} {P Q : Finset (Finset α)}
    (hP : IsPartialPairing U P) (hQ : IsPerfectPairing (U \ pairingSupport P) Q) :
    IsPerfectPairing U (P ∪ Q) ∧ Disjoint P Q := by
  have hcross : ∀ e ∈ P, ∀ d ∈ Q, Disjoint e d := by
    intro e he d hd
    apply Finset.disjoint_left.mpr
    intro i hie hid
    have hiP := (mem_pairingSupport i P).2 ⟨e, he, hie⟩
    have hiQ := hQ.1.2.2 ((mem_pairingSupport i Q).2 ⟨d, hd, hid⟩)
    exact (Finset.mem_sdiff.mp hiQ).2 hiP
  have hdis : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro e heP heQ
    have he := hP.1 e heP
    have hne : e.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i, hi⟩ := hne
    exact Finset.disjoint_left.mp (hcross e heP e heQ) hi hi
  have hsup : pairingSupport (P ∪ Q) = U := by
    ext i
    simp only [mem_pairingSupport, Finset.mem_union]
    constructor
    · rintro ⟨e, heP | heQ, hie⟩
      · exact hP.2.2 ((mem_pairingSupport i P).2 ⟨e, heP, hie⟩)
      · exact (Finset.mem_sdiff.mp (hQ.1.2.2
          ((mem_pairingSupport i Q).2 ⟨e, heQ, hie⟩))).1
    · intro hiU
      by_cases hiP : i ∈ pairingSupport P
      · obtain ⟨e, he, hie⟩ := (mem_pairingSupport i P).1 hiP
        exact ⟨e, Or.inl he, hie⟩
      · have hiQ : i ∈ pairingSupport Q := hQ.2.symm ▸ Finset.mem_sdiff.mpr ⟨hiU, hiP⟩
        obtain ⟨e, he, hie⟩ := (mem_pairingSupport i Q).1 hiQ
        exact ⟨e, Or.inr he, hie⟩
  refine ⟨⟨⟨?_, ?_, hsup.le⟩, hsup⟩, hdis⟩
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact hP.1 e he
    · exact hQ.1.1 e he
  · intro e he d hd hed
    rcases Finset.mem_union.mp he with he | he <;>
      rcases Finset.mem_union.mp hd with hd | hd
    · exact hP.2.1 he hd hed
    · exact hcross e he d hd
    · exact (hcross d hd e he).symm
    · exact hQ.1.2.1 he hd hed

/-- Choosing some pairs in a perfect pairing is equivalent to a partial pairing and a
perfect pairing of its uncovered labels. Consequently additive edge weights expand
without any ordering or factorial factor. -/
theorem finitePairingPolynomial_add (U : Finset α) (c d : Finset α → ℝ) :
    finitePairingPolynomial U (fun e => c e + d e) =
      ∑ P : Finset (Finset α) with IsPartialPairing U P,
        (∏ e ∈ P, c e) * finitePairingPolynomial (U \ pairingSupport P) d := by
  classical
  unfold finitePairingPolynomial
  simp_rw [Finset.prod_add]
  let X := (Finset.univ : Finset (Finset (Finset α) × Finset (Finset α))).filter
    (fun x => IsPerfectPairing U x.1 ∧ x.2 ⊆ x.1)
  let Z := (Finset.univ : Finset (Finset (Finset α) × Finset (Finset α))).filter
    (fun z => IsPartialPairing U z.1 ∧ IsPerfectPairing (U \ pairingSupport z.1) z.2)
  have hx : ∀ x, x ∈ X ↔ IsPerfectPairing U x.1 ∧ x.2 ⊆ x.1 := by
    intro x; simp [X]
  have hz : ∀ z, z ∈ Z ↔ IsPartialPairing U z.1 ∧
      IsPerfectPairing (U \ pairingSupport z.1) z.2 := by
    intro z; simp [Z]
  have hsum :
      (∑ x ∈ X, (∏ e ∈ x.2, c e) * ∏ e ∈ x.1 \ x.2, d e) =
      ∑ z ∈ Z, (∏ e ∈ z.1, c e) * ∏ e ∈ z.2, d e := by
    apply Finset.sum_nbij' (fun x => (x.2, x.1 \ x.2))
      (fun z => (z.1 ∪ z.2, z.1))
    · intro x h
      exact (hz _).2 (pairing_remainder ((hx x).1 h).1 ((hx x).1 h).2)
    · intro z h
      obtain ⟨hP, hQ⟩ := (hz z).1 h
      exact (hx _).2 ⟨(pairing_join hP hQ).1, Finset.subset_union_left⟩
    · intro x h
      apply Prod.ext
      · exact Finset.union_sdiff_of_subset ((hx x).1 h).2
      · rfl
    · intro z h
      apply Prod.ext
      · rfl
      · exact Finset.union_sdiff_cancel_left (pairing_join ((hz z).1 h).1 ((hz z).1 h).2).2
    · intro x h
      rfl
  have hpower (M : Finset (Finset α)) (F : Finset (Finset α) → ℝ) :
      (∑ P ∈ M.powerset, F P) =
        ∑ P : Finset (Finset α), if P ⊆ M then F P else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext P
    simp
  simp only [X, Z, Finset.sum_filter, Fintype.sum_prod_type, ite_and] at hsum
  simp_rw [hpower]
  simp only [Finset.sum_filter, Finset.mul_sum]
  simpa only [Finset.sum_ite_irrel, Finset.sum_const_zero, mul_ite, mul_zero] using hsum

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

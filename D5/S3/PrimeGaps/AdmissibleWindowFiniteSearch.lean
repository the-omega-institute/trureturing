/- GID: D5/S3/PrimeGaps/AdmissibleWindowFiniteSearch
   generality: G
   mirror-B: D5/B/S3/PrimeGaps/AdmissibleWindowFiniteSearch
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Normalize admissible windows and reflect their existence into finite even-subset search. -/

import D5.S3.PrimeGaps.DHLAdmissibleDiameterTransfer
import D5.S3.PrimeGaps.PrimeGapAdmissibilityContractBridge

/-! # Complete finite search for admissible windows

The new content is completeness of normalization by the least offset, including
preservation of all-prime admissibility and the parity restriction. It supports
the paper's finite optimization claim: a negative finite search excludes every
admissible tuple in the given window. The small-prime cutoff is imported from
`finite_local_residue_blocking_criterion`, not proved again here.
-/

namespace D5.S3.PrimeGaps.AdmissibleWindowFiniteSearch

open D5.S3.Analytic.PrimeProducts.FiniteLocalResidueBlockingCriterion
open D5.S3.PrimeGaps.DHLAdmissibleDiameterTransfer
open D5.S3.PrimeGaps.PrimeGapAdmissibilityContractBridge

/-- The finite range of prime moduli sufficient for a natural tuple. -/
def SmallPrimeAdmissible (H : Finset Nat) : Prop :=
  ∀ p : Nat, p.Prime → p ≤ H.card →
    localResidueCount (H.image (fun h : Nat => (h : Int))) p < p

instance (H : Finset Nat) : Decidable (SmallPrimeAdmissible H) := by
  let bounded : Decidable (∀ p ∈ Finset.range (H.card + 1), p.Prime →
      localResidueCount (H.image (fun h : Nat => (h : Int))) p < p) :=
    @Finset.decidableDforallFinset Nat (Finset.range (H.card + 1))
      (fun p _ => p.Prime → localResidueCount (H.image (fun h : Nat => (h : Int))) p < p)
      (fun _ _ => inferInstance)
  exact @decidable_of_iff (SmallPrimeAdmissible H)
    (∀ p ∈ Finset.range (H.card + 1), p.Prime →
      localResidueCount (H.image (fun h : Nat => (h : Int))) p < p)
    (by simp only [SmallPrimeAdmissible, Finset.mem_range, Nat.lt_succ_iff];
        exact forall_congr' fun _ => ⟨fun h hp hle => h hle hp, fun h hle hp => h hp hle⟩)
    bounded

/-- Natural admissibility and the existing integer direct-residue API agree. -/
theorem naturalTupleAdmissible_iff_integer (H : Finset Nat) :
    NaturalTupleAdmissible H ↔
      DirectTupleAdmissible (H.image (fun h : Nat => (h : Int))) := by
  simp only [NaturalTupleAdmissible, DirectTupleAdmissible, Finset.mem_image,
    forall_exists_index, and_imp]
  simp

/-- Reuse the repository's exact finite cutoff at the natural-carrier boundary. -/
theorem naturalTupleAdmissible_iff_small_primes (H : Finset Nat) :
    NaturalTupleAdmissible H ↔ SmallPrimeAdmissible H := by
  rw [naturalTupleAdmissible_iff_integer, directTupleAdmissible_iff_local_residue]
  have hcard : (H.image (fun h : Nat => (h : Int))).card = H.card :=
    Finset.card_image_of_injective _ Int.ofNat_injective
  have hcut := (finite_local_residue_blocking_criterion _ H.card hcard).2
  constructor
  · intro h p hp _
    exact h p hp
  · intro h p hp
    exact hcut.mpr (fun q hq => h q.val q.property hq) ⟨p, hp⟩

/-- Shift the least element to zero, with the empty set normalized to itself. -/
def normalizeNatTuple (H : Finset Nat) : Finset Nat :=
  if h : H.Nonempty then H.image (fun x => x - H.min' h) else ∅

/-- Subtracting a common lower bound preserves omitted residue classes. -/
theorem naturalTupleAdmissible_sub (H : Finset Nat) (a : Nat)
    (ha : ∀ x ∈ H, a ≤ x) (hadm : NaturalTupleAdmissible H) :
    NaturalTupleAdmissible (H.image (fun x => x - a)) := by
  intro p hp
  obtain ⟨r, hr⟩ := hadm p hp
  refine ⟨r - (a : ZMod p), ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  rw [Nat.cast_sub (ha x hx)]
  exact fun heq => hr x hx (sub_left_inj.mp heq)

/-- Normalization preserves cardinality, admissibility, and the window bound,
and supplies a zero member. -/
theorem normalizeNatTuple_spec (H : Finset Nat) (B : Nat)
    (hne : H.Nonempty) (hadm : NaturalTupleAdmissible H)
    (hB : ∀ x ∈ H, x ≤ B) :
    (normalizeNatTuple H).card = H.card ∧
      0 ∈ normalizeNatTuple H ∧
      NaturalTupleAdmissible (normalizeNatTuple H) ∧
      ∀ x ∈ normalizeNatTuple H, x ≤ B := by
  rw [normalizeNatTuple, dif_pos hne]
  refine ⟨Finset.card_image_iff.mpr ?_, ?_,
    naturalTupleAdmissible_sub H _ (fun x hx => H.min'_le x hx) hadm, ?_⟩
  · intro x hx y hy hxy
    change x - H.min' hne = y - H.min' hne at hxy
    have hax := H.min'_le x hx
    have hay := H.min'_le y hy
    omega
  · exact Finset.mem_image.mpr ⟨H.min' hne, H.min'_mem hne, Nat.sub_self _⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (Nat.sub_le _ _).trans (hB y hy)

/-- An admissible tuple containing zero consists of even offsets; no cardinality
assumption is necessary. -/
theorem admissible_zero_even (H : Finset Nat) (h0 : 0 ∈ H)
    (hadm : NaturalTupleAdmissible H) : ∀ x ∈ H, Even x := by
  obtain ⟨a, ha⟩ := hadm 2 Nat.prime_two
  have ha0 := ha 0 h0
  have ha1 : a = 1 := by
    have htwo : ∀ z : ZMod 2, (0 : ZMod 2) ≠ z → z = 1 := by decide
    exact htwo a (by simpa only [Nat.cast_zero] using ha0)
  intro x hx
  apply ZMod.natCast_eq_zero_iff_even.mp
  have hxa := ha x hx
  have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hcases (x : ZMod 2) with hz | hz
  · exact hz
  · exact False.elim (hxa (hz.trans ha1.symm))

/-- Every bounded natural set is exactly the value image of a finite bounded type. -/
theorem bounded_nat_finset_lift (H : Finset Nat) (B : Nat)
    (hB : ∀ x ∈ H, x ≤ B) :
    ∃ K : Finset (Fin (B + 1)), K.image Fin.val = H ∧ K.card = H.card := by
  let K : Finset (Fin (B + 1)) := Finset.univ.filter (fun x => x.val ∈ H)
  have heq : K.image Fin.val = H := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hy).2
    · intro hx
      exact Finset.mem_image.mpr ⟨⟨x, by have := hB x hx; omega⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
  refine ⟨K, heq, ?_⟩
  rw [← heq, Finset.card_image_of_injective _ Fin.val_injective]

/-- Positive-cardinality windows are equivalent to normalized bounded finite sets. -/
theorem exists_normalized_admissible_window_iff (k B : Nat) (hk : 0 < k) :
    AdmissibleWindowWitness k B ↔
      ∃ H : Finset (Fin (B + 1)), H.card = k ∧ (0 : Fin (B + 1)) ∈ H ∧
        SmallPrimeAdmissible (H.image Fin.val) := by
  constructor
  · rintro ⟨H, hc, ha, hB⟩
    have hn : H.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨hcard, hzero, hadm, hbound⟩ := normalizeNatTuple_spec H B hn ha hB
    obtain ⟨K, hK, hcK⟩ := bounded_nat_finset_lift (normalizeNatTuple H) B hbound
    refine ⟨K, hcK.trans (hcard.trans hc), ?_, ?_⟩
    · rw [← hK] at hzero
      obtain ⟨x, hx, hval⟩ := Finset.mem_image.mp hzero
      have hx0 : x = 0 := Fin.ext hval
      simpa [hx0] using hx
    · rw [hK]
      exact (naturalTupleAdmissible_iff_small_primes _).mp hadm
  · rintro ⟨H, hc, _, ha⟩
    refine ⟨H.image Fin.val, ?_, (naturalTupleAdmissible_iff_small_primes _).mpr ha, ?_⟩
    · rw [Finset.card_image_of_injective _ Fin.val_injective, hc]
    · intro x hx
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
      exact Nat.le_of_lt_succ y.isLt

/-- The normalized finite carrier inherits the parity restriction, including
singleton tuples. -/
theorem normalized_admissible_even {B : Nat} {H : Finset (Fin (B + 1))}
    (h0 : (0 : Fin (B + 1)) ∈ H)
    (hadm : NaturalTupleAdmissible (H.image Fin.val)) :
    ∀ x ∈ H, Even x.val := by
  have hz : 0 ∈ H.image Fin.val := Finset.mem_image.mpr ⟨0, h0, rfl⟩
  intro x hx
  exact admissible_zero_even _ hz hadm x.val (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

/-- An executable search over all normalized even subsets of the bounded carrier. -/
def admissibleWindowCheck (k B : Nat) : Bool :=
  @decide (∃ H ∈ ((Finset.range (B + 1)).filter (fun x => Even x)).powersetCard k,
    0 ∈ H ∧ SmallPrimeAdmissible H)
    (@Finset.decidableExistsAndFinset (Finset Nat)
      (((Finset.range (B + 1)).filter (fun x => Even x)).powersetCard k)
      (fun H => 0 ∈ H ∧ SmallPrimeAdmissible H) (fun _ => inferInstance))

/-- Soundness and completeness of finite normalized even search, for every
positive tuple size and every window width. -/
theorem admissibleWindowCheck_eq_true_iff (k B : Nat) (hk : 0 < k) :
    admissibleWindowCheck k B = true ↔ AdmissibleWindowWitness k B := by
  simp only [admissibleWindowCheck, decide_eq_true_eq,
    Finset.mem_powersetCard]
  constructor
  · rintro ⟨H, ⟨hsub, hc⟩, _, ha⟩
    refine ⟨H, hc, (naturalTupleAdmissible_iff_small_primes _).mpr ha, ?_⟩
    intro x hx
    have hmem := (Finset.mem_filter.mp (hsub hx)).1
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hmem)
  · rintro ⟨H, hc, ha, hB⟩
    have hn : H.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨hcard, hzero, hadm, hbound⟩ := normalizeNatTuple_spec H B hn ha hB
    refine ⟨normalizeNatTuple H, ⟨?_, hcard.trans hc⟩, hzero,
      (naturalTupleAdmissible_iff_small_primes _).mp hadm⟩
    intro x hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound x hx)),
        admissible_zero_even _ hzero hadm x hx⟩

end D5.S3.PrimeGaps.AdmissibleWindowFiniteSearch

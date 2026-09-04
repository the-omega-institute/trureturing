/- GID: D5/S3/ArithUnits/CyclicPlaneTwelveMultiplierObstruction
   generality: I
   mirror-B: D5/B/S3/ArithUnits/CyclicPlaneTwelveMultiplierObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Doubling orbits obstruct a thirteen-element affine multiplier relation modulo 157. -/

import Mathlib

/- Library-search audit trail (2026-09-05):
   * Current D5 searches found no declaration about a cyclic projective plane,
     a difference set in `ZMod 157`, or the multiplier-two obstruction below.
   * Pinned Mathlib searches found no complete invariant-set divisibility or
     `ZMod 157` order theorem. The proof uses its general orbit equivalence
     `MulAction.selfEquivOrbitsQuotientProd`, `Nat.card_zpowers`, and
     `orderOf_eq_of_pow_and_pow_div_prime` rather than reproving them. -/

namespace D5.S3.ArithUnits.CyclicPlaneTwelveMultiplierObstruction

/-- Translating an affine multiplier relation by a fixed point turns it into
an invariant-set relation. -/
theorem affine_multiplier_conjugacy
    {R : Type*} [CommRing R] [DecidableEq R]
    (D : Finset R) (m shift center : R)
    (hfixed : m * center = center + shift)
    (hrel : D.image (fun x => m * x) = D.image (fun x => x + shift)) :
    (D.image (fun x => x - center)).image (fun x => m * x) =
      D.image (fun x => x - center) := by
  calc
    (D.image (fun x => x - center)).image (fun x => m * x) =
        (D.image (fun x => m * x)).image (fun x => x - m * center) := by
      simp only [Finset.image_image]
      apply Finset.image_congr
      intro x hx
      dsimp only [Function.comp_apply]
      ring
    _ = (D.image (fun x => x + shift)).image (fun x => x - m * center) := by
      rw [hrel]
    _ = D.image (fun x => x - center) := by
      simp only [Finset.image_image]
      apply Finset.image_congr
      intro x hx
      dsimp only [Function.comp_apply]
      rw [hfixed]
      ring

/-- The nonzero part of an invariant finite subset of a prime residue field is
a union of free cyclic orbits. -/
theorem orderOf_dvd_card_erase_zero_of_image_mul_eq
    {p : Nat} [Fact p.Prime] (u : (ZMod p)ˣ) (S : Finset (ZMod p))
    (hinv : S.image (fun x => (u : ZMod p) * x) = S) :
    orderOf u ∣ (S.erase 0).card := by
  classical
  have hstep : ∀ {x : ZMod p}, x ∈ S → (u : ZMod p) * x ∈ S := by
    intro x hx
    rw [← hinv]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hpow : ∀ (n : Nat) {x : ZMod p}, x ∈ S → (u : ZMod p) ^ n * x ∈ S := by
    intro n
    induction n with
    | zero =>
        intro x hx
        simpa using hx
    | succ n ih =>
        intro x hx
        simpa [pow_succ', mul_assoc] using hstep (ih hx)
  let H := Subgroup.zpowers u
  let T : SubMulAction H (ZMod p) :=
    { carrier := {x | x ∈ S ∧ x ≠ 0}
      smul_mem' := by
        intro a x hx
        change x ∈ S ∧ x ≠ 0 at hx
        change (((a.1 : (ZMod p)ˣ) : ZMod p) * x ∈ S) ∧
          (((a.1 : (ZMod p)ˣ) : ZMod p) * x ≠ 0)
        let hu : IsOfFinOrder u := isOfFinOrder_of_finite u
        let n : Fin (orderOf u) := (finEquivZPowers hu).symm a
        have haU : u ^ (n : Nat) = (a : H) :=
          pow_finEquivZPowers_symm_apply hu a
        have ha : (u : ZMod p) ^ (n : Nat) = ((a.1 : (ZMod p)ˣ) : ZMod p) := by
          simpa using congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) haU
        constructor
        · rw [← ha]
          exact hpow n hx.1
        · exact mul_ne_zero (Units.ne_zero _) hx.2 }
  let eT : T ≃ ↥(S.erase 0) :=
    Equiv.subtypeEquivRight (fun x => by
      change (x ∈ S ∧ x ≠ 0) ↔ x ∈ S.erase 0
      simp [and_comm])
  have hTcard : Nat.card T = (S.erase 0).card := by
    calc
      Nat.card T = Nat.card ↥(S.erase 0) := Nat.card_congr eT
      _ = (S.erase 0).card := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_coe _
  let e := MulAction.selfEquivOrbitsQuotientProd
    (G := H) (X := T) (fun b => by
      apply (Subgroup.eq_bot_iff_forall _).mpr
      intro a ha
      rw [MulAction.mem_stabilizer_iff] at ha
      apply Subtype.ext
      apply Units.ext
      change ((a.1 : (ZMod p)ˣ) : ZMod p) = 1
      apply mul_right_cancel₀ b.2.2
      simpa only [SubMulAction.val_smul, Subgroup.smul_def, Units.smul_def, smul_eq_mul,
        one_mul] using congrArg (fun z : T => (z : ZMod p)) ha)
  have hcard : Nat.card T =
      Nat.card (Quotient (MulAction.orbitRel H T)) * Nat.card H := by
    calc
      Nat.card T = Nat.card (Quotient (MulAction.orbitRel H T) × H) :=
        Nat.card_congr e
      _ = Nat.card (Quotient (MulAction.orbitRel H T)) * Nat.card H :=
        Nat.card_prod _ _
  rw [hTcard, Nat.card_zpowers u] at hcard
  refine ⟨Nat.card (Quotient (MulAction.orbitRel H T)), ?_⟩
  rw [hcard, Nat.mul_comm]

/-- The multiplicative order of two modulo 157 is 52. -/
theorem orderOf_two_zmod157 : orderOf (2 : ZMod 157) = 52 := by
  refine orderOf_eq_of_pow_and_pow_div_prime (x := (2 : ZMod 157))
    (n := 52) (by norm_num) ?_ ?_
  · decide
  · intro q hq hq52
    have hqle : q ≤ 52 := Nat.le_of_dvd (by norm_num) hq52
    interval_cases q
    all_goals norm_num at hq
    all_goals norm_num at hq52
    all_goals decide

private def twoUnit157 : (ZMod 157)ˣ :=
  ZMod.unitOfCoprime 2 (by norm_num)

/-- A doubling-invariant subset of `ZMod 157` has cardinality congruent to
zero or one modulo 52; the exceptional point is zero. -/
theorem card_of_invariant_under_mul_two (S : Finset (ZMod 157))
    (hinv : S.image (fun x => 2 * x) = S) :
    S.card % 52 ∈ ({0, 1} : Set Nat) := by
  letI : Fact (Nat.Prime 157) := ⟨by norm_num⟩
  have hu : orderOf twoUnit157 = 52 := by
    calc
      orderOf twoUnit157 = orderOf ((twoUnit157 : (ZMod 157)ˣ) : ZMod 157) :=
        (orderOf_injective (Units.coeHom (ZMod 157)) Units.val_injective twoUnit157).symm
      _ = orderOf (2 : ZMod 157) := by simp [twoUnit157]
      _ = 52 := orderOf_two_zmod157
  have hinv' : S.image (fun x => (twoUnit157 : ZMod 157) * x) = S := by
    simpa [twoUnit157] using hinv
  have hd := orderOf_dvd_card_erase_zero_of_image_mul_eq twoUnit157 S hinv'
  rw [hu] at hd
  by_cases hzero : (0 : ZMod 157) ∈ S
  · have hcard := Finset.card_erase_add_one hzero
    obtain ⟨k, hk⟩ := hd
    rw [← hcard, hk]
    simp [Nat.add_mod]
  · rw [Finset.erase_eq_of_notMem hzero] at hd
    simp [Nat.mod_eq_zero_of_dvd hd]

/-- No thirteen-element subset of `ZMod 157` can be carried to a translate
of itself by doubling. -/
theorem multiplier_two_obstruction (D : Finset (ZMod 157))
    (hcard : D.card = 13) (g : ZMod 157) :
    D.image (fun x => 2 * x) ≠ D.image (fun x => x + g) := by
  intro hrel
  let S := D.image (fun x => x - g)
  have hinv : S.image (fun x => 2 * x) = S := by
    exact affine_multiplier_conjugacy D 2 g g (by ring) hrel
  have hSCard : S.card = 13 := by
    rw [show S = D.image (fun x => x - g) by rfl,
      Finset.card_image_of_injective]
    · exact hcard
    · intro x y hxy
      simpa using congrArg (fun z => z + g) hxy
  have hmod := card_of_invariant_under_mul_two S hinv
  rw [hSCard] at hmod
  norm_num at hmod

/-- The explicit thirteen-element set used for the non-vacuity witness. -/
def thirteenResidues : Finset (ZMod 157) :=
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}

/-- The explicit set has cardinality thirteen, while its doubling image is
not its zero translate. -/
theorem thirteenResidues_witness :
    thirteenResidues.card = 13 ∧
      thirteenResidues.image (fun x => 2 * x) ≠
        thirteenResidues.image (fun x => x + 0) := by
  constructor <;> decide

/-- A complete nonzero doubling orbit modulo seven. -/
def doublingOrbitSeven : Finset (ZMod 7) := {1, 2, 4}

/-- Modulo seven, two has order three and its explicit three-element orbit is
doubling-invariant. -/
theorem doublingOrbitSeven_witness :
    orderOf (2 : ZMod 7) = 3 ∧
      doublingOrbitSeven.card = 3 ∧
        doublingOrbitSeven.image (fun x => 2 * x) = doublingOrbitSeven := by
  constructor
  · rw [orderOf_eq_iff (by norm_num)]
    constructor
    · decide
    · intro m hm hmpos
      interval_cases m
      all_goals decide
  · constructor <;> decide

-- Step-6 fidelity witnesses for conditional hypotheses and inhabited domains.
example :
    ∃ (D : Finset (ZMod 7)) (m shift center : ZMod 7),
      m * center = center + shift ∧
        D.image (fun x => m * x) = D.image (fun x => x + shift) := by
  refine ⟨∅, 2, 0, 0, ?_, ?_⟩ <;> simp

example :
    ∃ S : Finset (ZMod 157), S.image (fun x => 2 * x) = S := by
  exact ⟨{0}, by decide⟩

example : ∃ D : Finset (ZMod 157), D.card = 13 :=
  ⟨thirteenResidues, thirteenResidues_witness.1⟩

example :
    ∃ u : (ZMod 7)ˣ,
      doublingOrbitSeven.image (fun x => (u : ZMod 7) * x) = doublingOrbitSeven := by
  refine ⟨ZMod.unitOfCoprime 2 (by norm_num), ?_⟩
  simpa using doublingOrbitSeven_witness.2.2

#print axioms affine_multiplier_conjugacy
#print axioms orderOf_dvd_card_erase_zero_of_image_mul_eq
#print axioms orderOf_two_zmod157
#print axioms card_of_invariant_under_mul_two
#print axioms multiplier_two_obstruction
#print axioms thirteenResidues_witness
#print axioms doublingOrbitSeven_witness

end D5.S3.ArithUnits.CyclicPlaneTwelveMultiplierObstruction

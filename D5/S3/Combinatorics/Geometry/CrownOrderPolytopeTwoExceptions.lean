/- GID: D5/S3/Combinatorics/Geometry/CrownOrderPolytopeTwoExceptions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/CrownOrderPolytopeTwoExceptions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointRecovery]
   utility: none
   digest: The two full endpoint fibers are precisely the missing two-block crown partitions.
   -/

import D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEndpointRecovery
import Mathlib.Data.Fintype.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

open D5.S3.Combinatorics.Geometry.CrownOrderPolytope

/-- `false` puts all original vertices with bottom; `true` puts them with top.
    The other endpoint is a singleton. -/
def crownExceptionalCode {n : ℕ} (b : Bool) : CrownAugmentedVertex n → Bool
  | .bottom => false
  | .vertex _ => b
  | .top => true

/-- The two actual exceptional CCPs of Proposition 3.3(iii), including their
    graph connectivity, quotient compatibility, and exactly two quotient blocks. -/
noncomputable def crownExceptionalCCP (n : ℕ) (b : Bool) :
    {P : CrownConnectedCompatiblePartition n // Nat.card (Quotient P.toSetoid) = 2} := by
  let code := @crownExceptionalCode n b
  let s := Setoid.ker code
  let G := crownPartitionGraph s
  have hbottom (i : Fin (2 * n)) (hb : b = false) : G.Reachable .bottom (.vertex i) := by
    apply SimpleGraph.Adj.reachable
    exact (SimpleGraph.fromRel_adj _ _ _).mpr
      ⟨by simp, Or.inl ⟨by change false = b; exact hb.symm, trivial⟩⟩
  have htop (i : Fin (2 * n)) (hb : b = true) : G.Reachable (.vertex i) .top := by
    apply SimpleGraph.Adj.reachable
    exact (SimpleGraph.fromRel_adj _ _ _).mpr
      ⟨by simp, Or.inl ⟨by change b = true; exact hb, trivial⟩⟩
  have hconnected : ∀ u v, s.r u v ↔ G.Reachable u v := by
    intro u v
    constructor
    · intro h
      change code u = code v at h
      cases u with
      | bottom =>
          cases v with
          | bottom => exact SimpleGraph.Reachable.refl _
          | vertex i => exact hbottom i h.symm
          | top => exact Bool.noConfusion h
      | top =>
          cases v with
          | bottom => exact Bool.noConfusion h
          | vertex i => exact (htop i h.symm).symm
          | top => exact SimpleGraph.Reachable.refl _
      | vertex i =>
          cases v with
          | bottom => exact (hbottom i h).symm
          | vertex j =>
              cases b with
              | false => exact (hbottom i rfl).symm.trans (hbottom j rfl)
              | true => exact (htop i rfl).trans (htop j rfl).symm
          | top => exact htop i h
    · rintro ⟨w⟩
      induction w with
      | nil => exact s.refl _
      | @cons u v w huv _ ih =>
          have he : s.r u v := by
            rcases ((SimpleGraph.fromRel_adj _ _ _).mp huv).2 with h | h
            · exact h.1
            · exact s.symm h.1
          exact s.trans he ih
  have hmono {u v : CrownAugmentedVertex n} (h : crownAugmentedLE u v) :
      code u ≤ code v := by
    cases u <;> cases v <;> cases b <;> simp_all [code, crownExceptionalCode, crownAugmentedLE]
  have hcompatible : ∀ {C D : Quotient s}, crownPartitionBlockLE s C D →
      crownPartitionBlockLE s D C → C = D := by
    have hle {C D : Quotient s} (h : crownPartitionBlockLE s C D) :
        Setoid.kerLift code C ≤ Setoid.kerLift code D := by
      induction h with
      | refl => exact le_rfl
      | tail _ h ih =>
          obtain ⟨u, v, rfl, rfl, huv⟩ := h
          exact ih.trans (hmono huv)
    intro C D hCD hDC
    exact Setoid.kerLift_injective code (le_antisymm (hle hCD) (hle hDC))
  refine ⟨⟨s, hconnected, hcompatible⟩, ?_⟩
  have hsurj : Function.Surjective code := by
    intro c
    cases c with
    | false => exact ⟨.bottom, rfl⟩
    | true => exact ⟨.top, rfl⟩
  exact (Nat.card_congr (Setoid.quotientKerEquivOfSurjective code hsurj)).trans (by simp)

private theorem crownOddBlockMerge_two_range {n : ℕ} (hn : 2 ≤ n)
    (P : {P : CrownConnectedCompatiblePartition n // Nat.card (Quotient P.toSetoid) = 2}) :
    (∃ a : CrownOddBlockSelectionOfCard n 2, crownOddBlockMerge hn (by omega) a = P) ↔
      ∀ b : Bool, P ≠ crownExceptionalCCP n b := by
  classical
  have crownTwoCCP_separate {n : ℕ}
      (P : CrownConnectedCompatiblePartition n) (hcard : Nat.card (Quotient P.toSetoid) = 2) :
      ¬ P.toSetoid.r .bottom .top := by
    intro hbt
    have hall (u : CrownAugmentedVertex n) : P.toSetoid.r .bottom u := by
      apply Quotient.exact
      apply P.compatible
      · exact Relation.ReflTransGen.single
          ⟨.bottom, u, rfl, rfl, by cases u <;> trivial⟩
      · exact Relation.ReflTransGen.single
          ⟨u, .top, rfl, (Quotient.sound hbt).symm, by cases u <;> trivial⟩
    have hs : Function.Surjective (fun _ : Unit => (Quotient.mk'' .bottom : Quotient P.toSetoid)) := by
      intro C
      obtain ⟨u, rfl⟩ := Quotient.exists_rep C
      exact ⟨(), Quotient.sound (hall u)⟩
    have hc := Nat.card_le_card_of_surjective _ hs
    have hunit : Nat.card Unit = 1 := by simp
    rw [hunit, hcard] at hc
    omega

  have crownTwoCCP_full_fiber {n : ℕ}
      (P : CrownConnectedCompatiblePartition n) (hsep : ¬ P.toSetoid.r .bottom .top)
      (b : Bool) (hfull : ∀ i, P.toSetoid.r (if b then .top else .bottom) (.vertex i)) :
      P = (crownExceptionalCCP n b).val := by
    have heq : P.toSetoid = (crownExceptionalCCP n b).val.toSetoid := by
      apply Setoid.ext
      intro u v
      change P.toSetoid.r u v ↔ crownExceptionalCode b u = crownExceptionalCode b v
      have hnot (i : Fin (2 * n)) :
          ¬ P.toSetoid.r (if b then .bottom else .top) (.vertex i) := by
        intro h
        cases b with
        | false => exact hsep (P.toSetoid.trans (hfull i) (P.toSetoid.symm h))
        | true => exact hsep (P.toSetoid.trans h (P.toSetoid.symm (hfull i)))
      have hvertices (i j : Fin (2 * n)) : P.toSetoid.r (.vertex i) (.vertex j) :=
        P.toSetoid.trans (P.toSetoid.symm (hfull i)) (hfull j)
      have hsep' : ¬ P.toSetoid.r .top .bottom := fun h => hsep (P.toSetoid.symm h)
      cases b <;> cases u <;> cases v <;>
        simp_all [crownExceptionalCode, P.toSetoid.comm]
    have hext (A B : CrownConnectedCompatiblePartition n)
        (h : A.toSetoid = B.toSetoid) : A = B := by
      cases A
      cases B
      cases h
      rfl
    exact hext _ _ heq
  have hsep := crownTwoCCP_separate P.val P.property
  constructor
  · rintro ⟨a, ha⟩ b heq
    have himage := (twoSidedMergeCCP_range_iff hn
      (crownOddBlockMerge hn (by omega : 2 ≤ 2) a).val).mp ⟨a.val, rfl⟩
    rw [ha, heq] at himage
    cases b with
    | false =>
        obtain ⟨i, hi⟩ := himage.2.1
        exact hi rfl
    | true =>
        obtain ⟨i, hi⟩ := himage.2.2
        exact hi rfl
  · intro hnot
    have hbottom : ∃ i, ¬ P.val.toSetoid.r .bottom (.vertex i) := by
      by_contra h
      apply hnot false
      apply Subtype.ext
      exact crownTwoCCP_full_fiber P.val hsep false (by simpa using h)
    have htop : ∃ i, ¬ P.val.toSetoid.r .top (.vertex i) := by
      by_contra h
      apply hnot true
      apply Subtype.ext
      exact crownTwoCCP_full_fiber P.val hsep true (by simpa using h)
    obtain ⟨a, ha⟩ := (twoSidedMergeCCP_range_iff hn P.val).mpr ⟨hsep, hbottom, htop⟩
    have hc := (twoSidedMergeCCP_card hn a.val.1 a.val.2 a.property.2 a.property.1).2.2
    rw [ha, P.property] at hc
    refine ⟨⟨a, by omega⟩, ?_⟩
    exact Subtype.ext ha

/-- Proposition 3.3(iii) for actual connected compatible partitions: the merger
    image and the two full endpoint fibers give a disjoint exhaustive parametrization,
    and consequently the number of two-block CCPs is `|A₂| + 2`. -/
theorem crownOddBlockMerge_two_card {n : ℕ} (hn : 2 ≤ n) :
    Function.Bijective (Sum.elim (crownOddBlockMerge hn (by omega : 2 ≤ 2))
      (crownExceptionalCCP n)) ∧
    Nat.card {P : CrownConnectedCompatiblePartition n // Nat.card (Quotient P.toSetoid) = 2} =
      Nat.card (CrownOddBlockSelectionOfCard n 2) + 2 := by
  classical
  let f := crownOddBlockMerge hn (by omega : 2 ≤ 2)
  let e := crownExceptionalCCP n
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply twoSidedMergeCCP_injective hn
    exact congrArg Subtype.val hab
  have he : Function.Injective e := by
    intro a b hab
    let i : Fin (2 * n) := ⟨0, by omega⟩
    have h := congrArg (fun P => P.val.toSetoid.r .bottom (.vertex i)) hab
    change (false = a) = (false = b) at h
    cases a <;> cases b <;> simp_all
  have hdisjoint (a : CrownOddBlockSelectionOfCard n 2) (b : Bool) : f a ≠ e b :=
    (crownOddBlockMerge_two_range hn (f a)).mp ⟨a, rfl⟩ b
  have hbij : Function.Bijective (Sum.elim f e) := by
    constructor
    · intro a b hab
      cases a with
      | inl a =>
          cases b with
          | inl b => exact congrArg Sum.inl (hf hab)
          | inr b => exact (hdisjoint a b hab).elim
      | inr a =>
          cases b with
          | inl b => exact (hdisjoint b a hab.symm).elim
          | inr b => exact congrArg Sum.inr (he hab)
    · intro P
      by_cases h : ∃ b, P = e b
      · obtain ⟨b, hb⟩ := h
        exact ⟨Sum.inr b, hb.symm⟩
      · obtain ⟨a, ha⟩ := (crownOddBlockMerge_two_range hn P).mpr (by simpa using h)
        exact ⟨Sum.inl a, ha⟩
  refine ⟨hbij, ?_⟩
  let : Finite (CrownConnectedCompatiblePartition n) :=
    Finite.of_injective (fun P : CrownConnectedCompatiblePartition n => P.toSetoid.r) (by
      intro P Q h
      have hs : P.toSetoid = Q.toSetoid := Setoid.ext fun u v =>
        Iff.of_eq (congrFun (congrFun h u) v)
      cases P
      cases Q
      cases hs
      rfl)
  letI : Finite (CrownOddBlockSelectionOfCard n 2) := Finite.of_injective f hf
  have hc := Nat.card_congr (Equiv.ofBijective (Sum.elim f e) hbij)
  rw [Nat.card_sum] at hc
  simpa using hc.symm

end D5.S3.Combinatorics.Geometry.CrownOrderPolytopeEnumeration

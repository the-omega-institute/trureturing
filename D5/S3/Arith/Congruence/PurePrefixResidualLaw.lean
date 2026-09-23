/- GID: D5/S3/Arith/Congruence/PurePrefixResidualLaw
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/PurePrefixResidualLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact rational residual laws from actual forbidden-prefix geometry. -/

import D5.S3.Arith.Congruence.ConditionalComparison.ThreePrime.Probability

/-!
The live construction prunes actual forbidden cylinders by their shortest
forbidden ancestors. Prefix overlap forces nesting, so the retained cylinders
are disjoint and have exactly the original union. The same geometry computes
all residual prefix probabilities, rather than assuming disjointness or
postulating their caps. Probability conditioning and individual prefix counts
are reused directly from the licensed upstream development.

Repository and pinned upstream tree laws, Mathlib finite unions and Kraft
bounds, and public Loogle searches supplied no exact residual-cylinder law
for this arbitrary forbidden family. This is symbolic finite-height geometry,
not enumeration, a certified instance, a checker, or a numerical reduction.
-/

open scoped BigOperators
open Erdos7 Erdos7.CappedGain

namespace D5.S3.Arith.Congruence.PurePrefixResidualLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Retain precisely the positive-depth forbidden words with no shorter
forbidden ancestor. -/
noncomputable def minimalForbiddenDepths {p H : ℕ} (f : ForbiddenPrefixesOf p H) :
    Finset (Fin (H + 1)) := by
  classical
  exact Finset.univ.filter fun d => 0 < d.val ∧
    ∀ e : Fin (H + 1), 0 < e.val → ∀ hed : e.val < d.val,
      ¬ HasPrefix (f d) (f e) hed.le

/-- The test prefix is contained in a retained forbidden cylinder. -/
def blocked {p H : ℕ} (f : ForbiddenPrefixesOf p H)
    (d : Fin (H + 1)) (u : Prefix p d.val) : Prop :=
  ∃ e ∈ minimalForbiddenDepths f, ∃ hed : e.val ≤ d.val,
    HasPrefix u (f e) hed

/-- Retained forbidden cylinders contained in the test cylinder. -/
noncomputable def forbiddenDescendants {p H : ℕ} (f : ForbiddenPrefixesOf p H)
    (d : Fin (H + 1)) (u : Prefix p d.val) : Finset (Fin (H + 1)) := by
  classical
  exact (minimalForbiddenDepths f).filter fun e =>
    ∃ hde : d.val ≤ e.val, HasPrefix (f e) u hde

open Classical in
/-- Every actual pure-prefix family has an exact supported rational law.
The normalizer and every residual cylinder probability retain all actual
prefix overlaps through the minimal forbidden cylinders. -/
theorem exists_exact_residual_law (p H : ℕ) (hp : 3 ≤ p)
    (f : ForbiddenPrefixesOf p H) :
    let Z : ℚ := 1 - ∑ e ∈ minimalForbiddenDepths f, 1 / (p : ℚ)^e.val
    0 < Z ∧ ∃ μ : FiniteLaw (Word p H),
      (∀ w, μ.weight w = if Good f w then 1 / ((p : ℚ)^H * Z) else 0) ∧
      ∀ (d : Fin (H + 1)) (u : Prefix p d.val),
        μ.prob (fun w => HasPrefix w u (indexedDepthLe d)) =
          if blocked f d u then 0 else
            (1 / (p : ℚ)^d.val -
              ∑ e ∈ forbiddenDescendants f d u, 1 / (p : ℚ)^e.val) / Z := by
  classical
  let : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  let ν := FiniteLaw.uniform (Word p H)
  let R := minimalForbiddenDepths f
  let Z : ℚ := 1 - ∑ e ∈ R, 1 / (p : ℚ)^e.val
  let hit (d : Fin (H + 1)) (w : Word p H) :=
    HasPrefix w (f d) (indexedDepthLe d)
  have trans {a b c : ℕ} (u : Prefix p a) (v : Prefix p b) (w : Word p c)
      (hab : a ≤ b) (hbc : b ≤ c)
      (hwv : HasPrefix w v hbc) (hvu : HasPrefix v u hab) :
      HasPrefix w u (hab.trans hbc) := by
    intro i
    exact (hwv ⟨i.val, Nat.lt_of_lt_of_le i.isLt hab⟩).trans (hvu i)
  have overlap {a b c : ℕ} (u : Prefix p a) (v : Prefix p b) (w : Word p c)
      (hab : a ≤ b) (hac : a ≤ c) (hbc : b ≤ c)
      (hwu : HasPrefix w u hac) (hwv : HasPrefix w v hbc) :
      HasPrefix v u hab := by
    intro i
    exact (hwv ⟨i.val, Nat.lt_of_lt_of_le i.isLt hab⟩).symm.trans (hwu i)
  have good_iff (w : Word p H) :
      Good f w ↔ ∀ d : Fin (H + 1), 0 < d.val → ¬ hit d w := by
    constructor
    · intro hw d hd
      cases d using Fin.cases with
      | zero => simp at hd
      | succ i => exact hw i
    · intro hw i
      exact hw i.succ (by simp)
  have root_spec (d : Fin (H + 1)) (hd : d ∈ R) :
      0 < d.val ∧ ∀ e : Fin (H + 1), 0 < e.val → ∀ hed : e.val < d.val,
        ¬ HasPrefix (f d) (f e) hed.le := (Finset.mem_filter.mp hd).2
  have bad_iff (w : Word p H) : ¬ Good f w ↔ ∃ d ∈ R, hit d w := by
    constructor
    · intro hw
      have hex : ∃ d : Fin (H + 1), 0 < d.val ∧ hit d w := by
        simpa only [good_iff, not_forall, not_not, exists_prop] using hw
      let S := Finset.univ.filter fun d : Fin (H + 1) => 0 < d.val ∧ hit d w
      have hS : S.Nonempty := by
        obtain ⟨d, hd, hh⟩ := hex
        exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, hh⟩⟩
      let d := S.min' hS
      have hd : d ∈ S := Finset.min'_mem S hS
      obtain ⟨hdpos, hhit⟩ := (Finset.mem_filter.mp hd).2
      refine ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdpos, ?_⟩, hhit⟩
      intro e he hed hde
      have hehit : hit e w := trans (f e) (f d) w hed.le (indexedDepthLe d) hhit hde
      have heS : e ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, hehit⟩
      have hmin : d ≤ e := Finset.min'_le S e heS
      exact (not_le_of_gt hed) hmin
    · rintro ⟨d, hd, hhit⟩ hgood
      exact (good_iff w).mp hgood d (root_spec d hd).1 hhit
  have unique_hit (d e : Fin (H + 1)) (hd : d ∈ R) (he : e ∈ R)
      (w : Word p H) (hwd : hit d w) (hwe : hit e w) : d = e := by
    by_contra hne
    have hv : d.val ≠ e.val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hv with hlt | hgt
    · exact (root_spec e he).2 d (root_spec d hd).1 hlt
        (overlap (f d) (f e) w hlt.le (indexedDepthLe d) (indexedDepthLe e) hwd hwe)
    · exact (root_spec d hd).2 e (root_spec e he).1 hgt
        (overlap (f e) (f d) w hgt.le (indexedDepthLe e) (indexedDepthLe d) hwe hwd)
  have prob_finset (T : Finset (Word p H)) :
      ν.prob (fun w => w ∈ T) = (T.card : ℚ) / (p : ℚ)^H := by
    dsimp [ν]
    rw [FiniteLaw.uniform_prob_eq_card]
    simp [Word, Fintype.card_subtype]
  have union_prob (S : Finset (Fin (H + 1))) (hS : S ⊆ R) :
      ν.prob (fun w => ∃ d ∈ S, hit d w) =
        ∑ d ∈ S, 1 / (p : ℚ)^d.val := by
    let E (d : Fin (H + 1)) := prefixWords (f d) (indexedDepthLe d)
    have hdisjoint : (S : Set (Fin (H + 1))).PairwiseDisjoint E := by
      intro d hd e he hne
      change Disjoint (E d) (E e)
      rw [Finset.disjoint_left]
      intro w hwd hwe
      exact hne (unique_hit d e (hS hd) (hS he) w
        ((mem_prefixWords _ _ _).mp hwd) ((mem_prefixWords _ _ _).mp hwe))
    calc
      _ = ν.prob (fun w => w ∈ S.biUnion E) :=
        ν.prob_congr _ _ (fun w => by simp [E, hit])
      _ = ((S.biUnion E).card : ℚ) / (p : ℚ)^H := prob_finset _
      _ = (∑ d ∈ S, (E d).card : ℚ) / (p : ℚ)^H := by
        rw [Finset.card_biUnion hdisjoint, Nat.cast_sum]
      _ = ∑ d ∈ S, (E d).card / (p : ℚ)^H := Finset.sum_div _ _ _
      _ = ∑ d ∈ S, 1 / (p : ℚ)^d.val := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [← prob_finset (E d)]
        change ν.prob (fun w => w ∈ prefixWords (f d) (indexedDepthLe d)) = _
        simp_rw [mem_prefixWords]
        exact uniform_prefix_prob (by omega) (f d) (indexedDepthLe d)
  have hmass : ν.prob (Good f) = Z := by
    have hbad := union_prob R (fun _ h => h)
    have he : ν.prob (fun w => ¬ Good f w) = ν.prob (fun w => ∃ d ∈ R, hit d w) :=
      ν.prob_congr _ _ bad_iff
    have htotal := ν.prob_add_not (Good f)
    rw [he, hbad] at htotal
    dsimp [Z]
    linarith
  have hpos : 0 < ν.prob (Good f) := good_mass_pos hp f
  have hZ : 0 < Z := by rwa [hmass] at hpos
  let μ := ν.condition (Good f) hpos
  refine ⟨hZ, μ, ?_, ?_⟩
  · intro w
    change (if Good f w then ν.weight w / ν.prob (Good f) else 0) = _
    rw [hmass]
    by_cases hw : Good f w
    · simp [hw, ν, FiniteLaw.uniform, Word, Z, R, div_eq_mul_inv, mul_comm]
    · simp [hw]
  · intro d u
    rw [FiniteLaw.condition_prob, hmass]
    by_cases hblocked : blocked f d u
    · rw [if_pos hblocked]
      have hz : ν.prob (fun w => Good f w ∧ HasPrefix w u (indexedDepthLe d)) = 0 := by
        rw [← ν.prob_false]
        apply ν.prob_congr
        intro w
        constructor
        · rintro ⟨hg, hu⟩
          obtain ⟨e, he, hed, hprefix⟩ := hblocked
          exact ((bad_iff w).mpr ⟨e, he,
            trans (f e) u w hed (indexedDepthLe d) hu hprefix⟩) hg
        · exact False.elim
      rw [hz, zero_div]
    · rw [if_neg hblocked]
      let S := forbiddenDescendants f d u
      have hSR : S ⊆ R := Finset.filter_subset _ _
      have hinter (w : Word p H) :
          (¬ Good f w ∧ HasPrefix w u (indexedDepthLe d)) ↔
            ∃ e ∈ S, hit e w := by
        constructor
        · rintro ⟨hbad, hu⟩
          obtain ⟨e, he, hehit⟩ := (bad_iff w).mp hbad
          have hde : d.val ≤ e.val := by
            by_contra h
            have hed : e.val ≤ d.val := by omega
            exact hblocked ⟨e, he, hed,
              overlap (f e) u w hed (indexedDepthLe e) (indexedDepthLe d) hehit hu⟩
          refine ⟨e, Finset.mem_filter.mpr ⟨he, hde, ?_⟩, hehit⟩
          exact overlap u (f e) w hde (indexedDepthLe d) (indexedDepthLe e) hu hehit
        · rintro ⟨e, he, hehit⟩
          obtain ⟨heR, hde, hprefix⟩ := Finset.mem_filter.mp he
          exact ⟨(bad_iff w).mpr ⟨e, heR, hehit⟩,
            trans u (f e) w hde (indexedDepthLe e) hehit hprefix⟩
      have hbadmass :
          ν.prob (fun w => ¬ Good f w ∧ HasPrefix w u (indexedDepthLe d)) =
            ∑ e ∈ S, 1 / (p : ℚ)^e.val :=
        (ν.prob_congr _ _ hinter).trans (union_prob S hSR)
      have hpartition :
          ν.prob (fun w => Good f w ∧ HasPrefix w u (indexedDepthLe d)) +
          ν.prob (fun w => ¬ Good f w ∧ HasPrefix w u (indexedDepthLe d)) =
          ν.prob (fun w => HasPrefix w u (indexedDepthLe d)) := by
        unfold FiniteLaw.prob FiniteLaw.expect
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro w hw
        by_cases hg : Good f w <;>
          by_cases hu : HasPrefix w u (indexedDepthLe d) <;> simp [hg, hu]
      rw [hbadmass, uniform_prefix_prob (by omega) u (indexedDepthLe d)] at hpartition
      congr 1
      linarith

#print axioms exists_exact_residual_law

end D5.S3.Arith.Congruence.PurePrefixResidualLaw

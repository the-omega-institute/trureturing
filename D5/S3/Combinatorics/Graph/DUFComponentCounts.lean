/- GID: D5/S3/Combinatorics/Graph/DUFComponentCounts
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DUFComponentCounts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: Exactly two reciprocal fibers belong to each saturated link component. -/

import D5.S3.Combinatorics.Graph.DUFComponents

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DUFComponentCounts

open Finset DUFStructure DUFCounting DUFComponents
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An unoriented component has two four-set sides; a side is not part of its identity. -/
def blockSide (H : Finset (Finset V)) (S : Finset V) (z : V × Finset V) : Prop :=
  ∃ A, CompleteBlock H z.1 A S ∧ z.2 = A ∪ S

/-- Four-star fibers occur in reciprocal pairs, one pair per actual link component. -/
theorem reciprocal_count (H : Finset (Finset V)) (hd : DUF H) (hc : CapFour H) :
    b H = 2 * B H := by
  let fs := (univ.powersetCard 4).filter fun S : Finset V => (fiber H S).card = 4
  have hpair (c : V) : Function.Injective (fun x : V => ({c, x} : Finset V)) := by
    intro x y hxy
    change ({c, x} : Finset V) = {c, y} at hxy
    have h1 : x ∈ ({c, y} : Finset V) := by rw [← hxy]; simp
    have h2 : y ∈ ({c, x} : Finset V) := by rw [hxy]; simp
    simp only [mem_insert, mem_singleton] at h1 h2
    grind
  have hswap (c : V) (A S : Finset V) (hb : CompleteBlock H c A S) :
      CompleteBlock H c S A := by
    refine ⟨hb.2.1, hb.1, hb.2.2.2.1, hb.2.2.1, hb.2.2.2.2.1.symm, ?_⟩
    intro s hs a ha
    simpa [pair_comm] using hb.2.2.2.2.2 a ha s hs
  have hmem (c : V) (A S : Finset V) (hb : CompleteBlock H c A S) :
      (c, A ∪ S) ∈ blocks H := by
    refine mem_filter.mpr ⟨?_, A, S, hb, rfl⟩
    simp only [mem_product, mem_univ, true_and, mem_powersetCard, subset_univ]
    rw [card_union_of_disjoint hb.2.2.2.2.1, hb.1, hb.2.1]
  have hfs (c : V) (A S : Finset V) (hb : CompleteBlock H c A S) : S ∈ fs := by
    refine mem_filter.mpr ⟨by simp [hb.2.1], ?_⟩
    rw [(block_fibers H hd hc c A S hb).1, DUFStructure.star,
      card_image_of_injective _ (hpair c), hb.1]
  have hleft : ∀ S ∈ fs, ((blocks H).filter (blockSide H S)).card = 1 := by
    intro S hS
    obtain ⟨hS4, hF4⟩ := mem_filter.mp hS
    obtain ⟨c, A, hb, hF, hrec, huniq⟩ :=
      reciprocal_four_fiber H hd hc S (mem_powersetCard.mp hS4).2 hF4
    have he : (blocks H).filter (blockSide H S) = {(c, A ∪ S)} := by
      ext z
      constructor
      · intro hz
        obtain ⟨D, hD, hzU⟩ := (mem_filter.mp hz).2
        have hzF := (block_fibers H hd hc z.1 D S hD).1
        obtain ⟨hzc, hDA⟩ := huniq z.1 D hD.2.2.1 hzF
        apply mem_singleton.mpr
        exact Prod.ext hzc (hzU.trans (congrArg (· ∪ S) hDA))
      · intro hz
        obtain rfl := mem_singleton.mp hz
        exact mem_filter.mpr ⟨hmem c A S hb, A, hb, rfl⟩
    rw [he, card_singleton]
  have hright : ∀ z ∈ blocks H, (fs.filter fun S => blockSide H S z).card = 2 := by
    intro z hz
    obtain ⟨A, S, hb, hzU⟩ := (mem_filter.mp hz).2
    have hAS : A ≠ S := by
      intro he
      have hdis := hb.2.2.2.2.1
      rw [he, disjoint_self] at hdis
      have hcard := hb.2.1
      simp [hdis] at hcard
    have he : (fs.filter fun T => blockSide H T z) = {A, S} := by
      ext T
      constructor
      · intro hT
        obtain ⟨D, hDT, hTU⟩ := (mem_filter.mp hT).2
        have hn := (block_component H hc z.1 A S hb).1
        have hn' := (block_component H hc z.1 D T hDT).1
        obtain ⟨x, hx⟩ := card_pos.mp (by rw [hb.1]; decide : 0 < A.card)
        have hxDT : x ∈ D ∪ T := by rw [← hTU, hzU]; exact mem_union_left _ hx
        rcases mem_union.mp hxDT with hxD | hxT
        · have hTS : T = S := (hn'.1 x hxD).symm.trans (hn.1 x hx)
          exact mem_insert.mpr (Or.inr (mem_singleton.mpr hTS))
        · have hDS : D = S := (hn'.2 x hxT).symm.trans (hn.1 x hx)
          have hTU' : T ∪ S = A ∪ S := by
            calc
              T ∪ S = S ∪ T := union_comm T S
              _ = D ∪ T := congrArg (· ∪ T) hDS.symm
              _ = z.2 := hTU.symm
              _ = A ∪ S := hzU
          have hTA : T = A := disjoint_injOn_union_left S
            (by simpa [hDS] using hDT.2.2.2.2.1) hb.2.2.2.2.1.symm hTU'
          exact mem_insert.mpr (Or.inl hTA)
      · intro hT
        rcases mem_insert.mp hT with hT | hT
        · subst T
          exact mem_filter.mpr ⟨hfs z.1 S A (hswap z.1 A S hb), S,
            hswap z.1 A S hb, hzU.trans (union_comm A S)⟩
        · have hTS := mem_singleton.mp hT
          subst T
          exact mem_filter.mpr ⟨hfs z.1 A S hb, A, hb, hzU⟩
    rw [he, card_pair hAS]
  have he := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := fs) (t := blocks H) (blockSide H)
  change (∑ S ∈ fs, ((blocks H).filter (blockSide H S)).card) =
    ∑ z ∈ blocks H, (fs.filter fun S => blockSide H S z).card at he
  rw [sum_congr rfl hleft, sum_congr rfl hright] at he
  simpa only [sum_const, smul_eq_mul, Nat.mul_one, Nat.mul_comm, Nat.one_mul, B, b, fs] using he

/-- The structural correction and the final subtraction-free counting identity. -/
theorem component_counting (H : Finset (Finset V)) (hu : ∀ e ∈ H, e.card = 3)
    (hd : DUF H) (hc : CapFour H) :
    q H 4 + a H = h H 4 + 4 * B H ∧ 8 * B H ≤ h H 4 ∧
    6 * H.card + a H + q H 2 + 2 * q H 1 + 3 * q H 0 + h H 1 + 3 * h H 0 =
      6 * (Fintype.card V).choose 2 + 4 * B H ∧
    21 * H.card + 10 * h H 0 + 3 * h H 1 + h H 3 ≤ 22 * (Fintype.card V).choose 2 ∧
    ((Fintype.card V).choose 2 < H.card → 2 ≤ B H ∧ 16 ≤ h H 4) := by
  have hb := reciprocal_count H hd hc
  obtain ⟨hf, hf', _⟩ := fiber_counts H hd hc
  obtain ⟨hbound, hid⟩ := counting_bound H hu hd hc
  refine ⟨by omega, by omega, by omega, hbound, ?_⟩
  intro hm
  constructor <;> omega

end D5.S3.Combinatorics.Graph.DUFComponentCounts

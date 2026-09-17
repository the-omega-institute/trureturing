/- GID: D5/S1/Words/Mechanical/RotationObservationCells
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/RotationObservationCells
   mirror-E: none(waiver:actual-symbolic-rotation-fiber-geometry)
   anchors: []
   utility: none
   digest: Actual rotation bits determine sorted half-open phase cells, sharp decoder radii, and the unique new split. -/

import D5.S1.Words.Mechanical.MechanicalBalance
import D5.S1.Words.Mechanical.FloorFractShift
import D5.S1.Words.ReturnWords.RotationGapArcs
import Mathlib.Tactic

/-!
# Actual observation fibers of an irrational rotation

The readout is the indicator of [1-alpha,1) evaluated on actual fractional
rotation iterates. Existing floor-carry and sorted-rotation-cut owners are
reused. The proof reconstructs every prefix floor from the bits, identifies
all cut tests, and proves that the bit fibers are the existing sorted arcs.
No cylinder geometry or cylinder-measure estimate is assumed.

The public results classify all uniform phase decoders on each observed
word and show that an extra bit splits exactly one old cell. Endpoint
conventions are literal: the source interval and every cell are left-closed,
right-open. No average-case prior or spectral-measure interpretation occurs.

Classical background: Julien and Putnam, Spectral triples for subshifts,
J. Funct. Anal. 270 (2016), Proposition 2.10 and Theorem 2.11,
DOI 10.1016/j.jfa.2015.12.002. Classical Sturmian complexity is not claimed
as a new discovery. The contribution is the actual-readout identification
and its sharp phase-decoding and refinement consumers over all phases.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S1.Words.Mechanical.RotationObservationCells

open Set
open D5.S1.Words
open D5.S1.Words.Mechanical
open D5.S1.Words.Mechanical.FloorFractShift
open D5.S1.Recurrence.RotationOrbitGapsPartition

/-- The first n actual binary window observations of phase x. -/
def rotationPrefix (alpha : Real) (n : Nat) (x : Real) : Fin n → Bool :=
  fun k => decide (1 - alpha ≤ Int.fract (x + (k.val : Real) * alpha))

private def cut (alpha : Real) (k : Nat) : Real :=
  1 - Int.fract (((k + 1 : Nat) : Real) * alpha)

private theorem phase_fract {x : Real} (hx : x ∈ Ico (0 : Real) 1) :
    Int.fract x = x := by
  have hf : ⌊x⌋ = 0 := Int.floor_eq_zero_iff.mpr hx
  simp [Int.fract, hf]

private theorem bit_is_mechanical {alpha : Real}
    (h0 : 0 ≤ alpha) (h1 : alpha < 1) (x : Real) (n : Nat) (k : Fin n) :
    rotationPrefix alpha n x k = lowerMechanicalWord alpha x k.val := by
  have hf : ⌊alpha⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩
  have hletter : lowerMechanicalLetter alpha x k.val =
      if 1 - alpha ≤ Int.fract (x + (k.val : Real) * alpha) then 1 else 0 := by
    unfold lowerMechanicalLetter
    rw [show x + (((k.val + 1 : Nat) : Real)) * alpha =
      (x + (k.val : Real) * alpha) + alpha by push_cast; ring]
    rw [floor_add_sub_floor, floor_fract_add_indicator,
      phase_fract ⟨h0, h1⟩, hf]
    simp
  by_cases h : 1 - alpha ≤ Int.fract (x + (k.val : Real) * alpha)
  · simp [rotationPrefix, lowerMechanicalWord, hletter, h]
  · simp [rotationPrefix, lowerMechanicalWord, hletter, h]

/-- Reconstructing all prefix floors from actual bits identifies the cut tests.
This is the arithmetic step missing from a theorem assuming cylinder bounds. -/
private theorem prefix_eq_iff_tests {alpha x y : Real}
    (h0 : 0 ≤ alpha) (h1 : alpha < 1)
    (hx : x ∈ Ico (0 : Real) 1) (hy : y ∈ Ico (0 : Real) 1) (n : Nat) :
    rotationPrefix alpha n x = rotationPrefix alpha n y ↔
      ∀ k < n, (cut alpha k ≤ x ↔ cut alpha k ≤ y) := by
  have hfloor (z : Real) (hz : z ∈ Ico (0 : Real) 1) (k : Nat) :
      ⌊z + (k : Real) * alpha⌋ = ⌊(k : Real) * alpha⌋ +
        if 1 - Int.fract ((k : Real) * alpha) ≤ z then 1 else 0 := by
    simpa only [phase_fract hz] using
      (floor_fract_add_indicator z ((k : Real) * alpha))
  have hfloor0x : ⌊x⌋ = 0 := Int.floor_eq_zero_iff.mpr hx
  have hfloor0y : ⌊y⌋ = 0 := Int.floor_eq_zero_iff.mpr hy
  constructor
  · intro hprefix
    have hletters (k : Nat) (hk : k < n) :
        lowerMechanicalLetter alpha x k = lowerMechanicalLetter alpha y k := by
      have he := congrFun hprefix ⟨k, hk⟩
      rw [bit_is_mechanical h0 h1, bit_is_mechanical h0 h1] at he
      rcases lowerMechanicalLetter_eq_zero_or_one (rho := x) h0 h1 k with hxk | hxk <;>
        rcases lowerMechanicalLetter_eq_zero_or_one (rho := y) h0 h1 k with hyk | hyk <;>
        simp_all [lowerMechanicalWord]
    have hfloors : ∀ k, k ≤ n →
        ⌊x + (k : Real) * alpha⌋ = ⌊y + (k : Real) * alpha⌋ := by
      intro k
      induction k with
      | zero => intro _; simpa using hfloor0x.trans hfloor0y.symm
      | succ k ih =>
          intro hk
          have hprev := ih (by omega)
          have hnext := hletters k (by omega)
          unfold lowerMechanicalLetter at hnext
          omega
    intro k hk
    have he := hfloors (k + 1) (by omega)
    rw [hfloor x hx, hfloor y hy] at he
    change (_ + if cut alpha k ≤ x then (1 : Int) else 0) =
      (_ + if cut alpha k ≤ y then (1 : Int) else 0) at he
    by_cases hcx : cut alpha k ≤ x <;> by_cases hcy : cut alpha k ≤ y <;>
      simp_all
  · intro htests
    have hfloors (k : Nat) (hk : k ≤ n) :
        ⌊x + (k : Real) * alpha⌋ = ⌊y + (k : Real) * alpha⌋ := by
      cases k with
      | zero => simpa using hfloor0x.trans hfloor0y.symm
      | succ k =>
          rw [hfloor x hx, hfloor y hy]
          have htest := htests k (by omega)
          change (_ + if cut alpha k ≤ x then (1 : Int) else 0) =
            (_ + if cut alpha k ≤ y then (1 : Int) else 0)
          by_cases hc : cut alpha k ≤ x
          · rw [if_pos hc, if_pos (htest.mp hc)]
          · rw [if_neg hc, if_neg (fun hy => hc (htest.mpr hy))]
    funext k
    rw [bit_is_mechanical h0 h1, bit_is_mechanical h0 h1]
    have hletter : lowerMechanicalLetter alpha x k.val =
        lowerMechanicalLetter alpha y k.val := by
      unfold lowerMechanicalLetter
      rw [hfloors (k.val + 1) (by omega), hfloors k.val k.isLt.le]
    simp only [lowerMechanicalWord, hletter]

private theorem cut_geometry (alpha : Real) (hi : Irrational alpha) (k : Nat) :
    cut alpha k ∈ Ioo (0 : Real) 1 ∧
      cut alpha k = Int.fract (((k + 1 : Nat) : Real) * (-alpha)) := by
  have hnz : Int.fract (((k + 1 : Nat) : Real) * alpha) ≠ 0 := by
    rw [Int.fract_ne_zero_iff]
    rintro ⟨z, hz⟩
    exact (hi.natCast_mul (Nat.succ_ne_zero k)).ne_int z hz.symm
  have hpos : 0 < Int.fract (((k + 1 : Nat) : Real) * alpha) :=
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hnz)
  constructor
  · dsimp [cut]
    constructor <;> linarith [Int.fract_lt_one (((k + 1 : Nat) : Real) * alpha)]
  · calc
      cut alpha k = Int.fract (-(((k + 1 : Nat) : Real) * alpha)) :=
        (Int.fract_neg hnz).symm
      _ = Int.fract (((k + 1 : Nat) : Real) * (-alpha)) := by congr 1; ring

private theorem cuts_eq_interior (alpha : Real) (hi : Irrational alpha) (n : Nat) :
    (Finset.range n).image (cut alpha) = rotationInteriorCutSet alpha (n + 1) := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    have hkg := cut_geometry alpha hi k
    rw [rotationInteriorCutSet]
    simp only [Finset.mem_erase]
    refine ⟨hkg.1.2.ne, hkg.1.1.ne', ?_⟩
    rw [rotationCutSet, Finset.mem_insert]
    right
    rw [rotationOrbit, Finset.mem_image]
    exact ⟨k + 1, Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega),
      hkg.2.symm⟩
  · intro hx
    rw [rotationInteriorCutSet] at hx
    simp only [Finset.mem_erase] at hx
    rcases hx with ⟨hx1, hx0, hx⟩
    rw [rotationCutSet, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact (hx1 rfl).elim
    · rw [rotationOrbit, Finset.mem_image] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      have hk0 : k ≠ 0 := by intro hk0; subst k; simp at hx0
      refine Finset.mem_image.mpr ⟨k - 1, Finset.mem_range.mpr ?_, ?_⟩
      · have := Finset.mem_range.mp hk; omega
      · rw [(cut_geometry alpha hi (k - 1)).2, show k - 1 + 1 = k by omega]

private theorem prefix_eq_iff_rank {alpha x y : Real} [Fact (Irrational alpha)]
    (h0 : 0 ≤ alpha) (h1 : alpha < 1)
    (hx : x ∈ Ico (0 : Real) 1) (hy : y ∈ Ico (0 : Real) 1) (n : Nat) :
    rotationPrefix alpha n x = rotationPrefix alpha n y ↔
      rotationGapRank alpha (n + 1) x = rotationGapRank alpha (n + 1) y := by
  let S := (Finset.range n).image (cut alpha)
  have hs : S = rotationInteriorCutSet alpha (n + 1) := cuts_eq_interior alpha Fact.out n
  have htests : (∀ k < n, (cut alpha k ≤ x ↔ cut alpha k ≤ y)) ↔
      S.filter (fun z => z ≤ x) = S.filter (fun z => z ≤ y) := by
    constructor
    · intro h
      ext z
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hz, hzx⟩
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
        exact ⟨Finset.mem_image.mpr ⟨k, hk, rfl⟩,
          (h k (Finset.mem_range.mp hk)).mp hzx⟩
      · rintro ⟨hz, hzy⟩
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
        exact ⟨Finset.mem_image.mpr ⟨k, hk, rfl⟩,
          (h k (Finset.mem_range.mp hk)).mpr hzy⟩
    · intro he k hk
      have hm : cut alpha k ∈ S := Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
      have := Finset.ext_iff.mp he (cut alpha k)
      simpa [hm] using this
  rw [prefix_eq_iff_tests h0 h1 hx hy, htests]
  rw [rotationGapRank, rotationGapRank, ← hs]
  constructor
  · exact congrArg Finset.card
  · intro he
    rcases le_total x y with hxy | hyx
    · apply Finset.eq_of_subset_of_card_le
      · intro z hz
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
          (Finset.mem_filter.mp hz).2.trans hxy⟩
      · exact he.ge
    · symm
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
          (Finset.mem_filter.mp hz).2.trans hyx⟩
      · exact he.le

/-- Every actual word fiber is the corresponding sorted phase interval.
Moreover, all centers and error radii valid for that word are classified:
b-R <= center <= a+R. Thus the optimum radius is (b-a)/2, with unique
center (a+b)/2, even though the right endpoint of the fiber is excluded. -/
theorem rotation_prefix_cell_and_decoder (alpha : Real) [Fact (Irrational alpha)]
    (h0 : 0 ≤ alpha) (h1 : alpha < 1) (n : Nat) (j : Fin (n + 1)) :
    let a := rotationCut alpha (n + 1) j.castSucc
    let b := rotationCut alpha (n + 1) j.succ
    {x : Real | x ∈ Ico 0 1 ∧ rotationPrefix alpha n x = rotationPrefix alpha n a} =
      Ico a b ∧
    ∀ center radius : Real,
      (∀ x ∈ Ico (0 : Real) 1,
        rotationPrefix alpha n x = rotationPrefix alpha n a → |x - center| ≤ radius) ↔
      b - radius ≤ center ∧ center ≤ a + radius := by
  let a := rotationCut alpha (n + 1) j.castSucc
  let b := rotationCut alpha (n + 1) j.succ
  have hab : a < b := (rotationCut alpha (n + 1)).strictMono j.castSucc_lt_succ
  have ha0 : 0 ≤ a := by
    calc
      0 = rotationCut alpha (n + 1) 0 := (rotation_cut_zero alpha (n + 1)).symm
      _ ≤ a := (rotationCut alpha (n + 1)).monotone (by simp)
  have hb1 : b ≤ 1 := by
    calc
      b ≤ rotationCut alpha (n + 1) (Fin.last (n + 1)) :=
        (rotationCut alpha (n + 1)).monotone (Fin.le_last _)
      _ = 1 := rotation_cut_last alpha (n + 1)
  have ha : a ∈ Ico (0 : Real) 1 := ⟨ha0, hab.trans_le hb1⟩
  have harank : rotationGapRank alpha (n + 1) a = j.val :=
    (rotation_gap_rank_iff_mem_rotation_gap_arc alpha (n + 1) ha j).mpr ⟨le_rfl, hab⟩
  have hfiber (x : Real) (hx : x ∈ Ico (0 : Real) 1) :
      rotationPrefix alpha n x = rotationPrefix alpha n a ↔ x ∈ Ico a b := by
    rw [prefix_eq_iff_rank h0 h1 hx ha, harank]
    exact rotation_gap_rank_iff_mem_rotation_gap_arc alpha (n + 1) hx j
  change {x : Real | x ∈ Ico 0 1 ∧ rotationPrefix alpha n x = rotationPrefix alpha n a} =
      Ico a b ∧ _
  constructor
  · ext x
    constructor
    · exact fun hx => (hfiber x hx.1).mp hx.2
    · intro hx
      have hx01 : x ∈ Ico (0 : Real) 1 := ⟨ha0.trans hx.1, hx.2.trans_le hb1⟩
      exact ⟨hx01, (hfiber x hx01).mpr hx⟩
  · intro center radius
    constructor
    · intro hbound
      have hleft := hbound a ha rfl
      have ha_le : a ≤ center + radius := by linarith [(abs_le.mp hleft).2]
      have hb_le : b ≤ center + radius := by
        by_contra hnot
        have hlt : center + radius < b := lt_of_not_ge hnot
        let x := (center + radius + b) / 2
        have hxab : x ∈ Ico a b := by dsimp [x]; constructor <;> linarith
        have hx01 : x ∈ Ico (0 : Real) 1 := ⟨ha0.trans hxab.1, hxab.2.trans_le hb1⟩
        have h := hbound x hx01 ((hfiber x hx01).mpr hxab)
        have := (abs_le.mp h).2
        dsimp [x] at this
        linarith
      constructor
      · linarith
      · linarith [(abs_le.mp hleft).1]
    · rintro ⟨hc0, hc1⟩ x hx hword
      have hxab := (hfiber x hx).mp hword
      rw [abs_le]
      constructor <;> linarith [hxab.1, hxab.2]

/-- One new observation introduces one genuinely new cut, lying strictly
inside an old cell. The exact equality test shows all changes occur across
that cut; explicit phases on its two sides share the old word and have
opposite next words. This is derived from the real rotation, not an assumed
list-refinement process. -/
theorem rotation_prefix_single_cut (alpha : Real) [Fact (Irrational alpha)]
    (h0 : 0 ≤ alpha) (h1 : alpha < 1) (n : Nat) :
    let beta := Int.fract (((n + 1 : Nat) : Real) * (-alpha))
    (∀ x ∈ Ico (0 : Real) 1, ∀ y ∈ Ico (0 : Real) 1,
      rotationPrefix alpha (n + 1) x = rotationPrefix alpha (n + 1) y ↔
      rotationPrefix alpha n x = rotationPrefix alpha n y ∧
        (beta ≤ x ↔ beta ≤ y)) ∧
    ∃! j : Fin (n + 1),
      rotationCut alpha (n + 1) j.castSucc < beta ∧
      beta < rotationCut alpha (n + 1) j.succ ∧
      ∃ x y : Real, x ∈ rotationGapArc alpha (n + 1) j ∧
        y ∈ rotationGapArc alpha (n + 1) j ∧ x < beta ∧ beta ≤ y ∧
        rotationPrefix alpha n x = rotationPrefix alpha n y ∧
        rotationPrefix alpha (n + 1) x ≠ rotationPrefix alpha (n + 1) y := by
  let beta := Int.fract (((n + 1 : Nat) : Real) * (-alpha))
  have hbeta : cut alpha n = beta := (cut_geometry alpha Fact.out n).2
  have hbeta01 : beta ∈ Ioo (0 : Real) 1 := by
    rw [← hbeta]
    exact (cut_geometry alpha Fact.out n).1
  have hstep (x : Real) (hx : x ∈ Ico (0 : Real) 1)
      (y : Real) (hy : y ∈ Ico (0 : Real) 1) :
      rotationPrefix alpha (n + 1) x = rotationPrefix alpha (n + 1) y ↔
      rotationPrefix alpha n x = rotationPrefix alpha n y ∧ (beta ≤ x ↔ beta ≤ y) := by
    rw [prefix_eq_iff_tests h0 h1 hx hy, prefix_eq_iff_tests h0 h1 hx hy]
    constructor
    · intro h
      exact ⟨fun k hk => h k (by omega), by simpa only [hbeta] using h n (by omega)⟩
    · rintro ⟨h, hb⟩ k hk
      by_cases hkn : k < n
      · exact h k hkn
      · have : k = n := by omega
        subst k
        simpa only [hbeta] using hb
  have hnew : beta ∉ rotationCutSet alpha (n + 1) := by
    intro hm
    rw [rotationCutSet, Finset.mem_insert] at hm
    rcases hm with hm | hm
    · exact hbeta01.2.ne hm
    · rw [rotationOrbit, Finset.mem_image] at hm
      obtain ⟨k, hk, heq⟩ := hm
      have hfract : Int.fract ((k : Real) * (-alpha)) =
          Int.fract (((n + 1 : Nat) : Real) * (-alpha)) := heq
      obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp hfract
      have hc : (k : Int) - ((n + 1 : Nat) : Int) ≠ 0 := by
        have := Finset.mem_range.mp hk
        omega
      have hi := (Fact.out : Irrational alpha).intCast_mul hc
      apply hi.ne_int (-z)
      push_cast
      rw [← hz]
      ring
  have hcover : beta ∈ ⋃ j : Fin (n + 1), rotationGapArc alpha (n + 1) j := by
    rw [iUnion_rotation_gap_arc]
    exact ⟨hbeta01.1.le, hbeta01.2⟩
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hcover
  have hjlo : rotationCut alpha (n + 1) j.castSucc < beta := by
    have hle : rotationCut alpha (n + 1) j.castSucc ≤ beta := hj.1
    apply lt_of_le_of_ne hle
    intro heq
    apply hnew
    rw [← heq]
    exact Finset.orderEmbOfFin_mem _ _ _
  have hjhi : beta < rotationCut alpha (n + 1) j.succ := hj.2
  let x := (rotationCut alpha (n + 1) j.castSucc + beta) / 2
  let y := beta
  have hxab : x ∈ rotationGapArc alpha (n + 1) j := by
    change rotationCut alpha (n + 1) j.castSucc ≤ x ∧ x < rotationCut alpha (n + 1) j.succ
    dsimp [x]
    constructor <;> linarith
  have hyab : y ∈ rotationGapArc alpha (n + 1) j := hj
  have hx01 : x ∈ Ico (0 : Real) 1 := by
    rw [← iUnion_rotation_gap_arc alpha (n + 1)]
    exact Set.mem_iUnion.mpr ⟨j, hxab⟩
  have hy01 : y ∈ Ico (0 : Real) 1 := ⟨hbeta01.1.le, hbeta01.2⟩
  have hxy : rotationPrefix alpha n x = rotationPrefix alpha n y := by
    rw [prefix_eq_iff_rank h0 h1 hx01 hy01]
    exact ((rotation_gap_rank_iff_mem_rotation_gap_arc alpha (n + 1) hx01 j).mpr hxab).trans
      ((rotation_gap_rank_iff_mem_rotation_gap_arc alpha (n + 1) hy01 j).mpr hyab).symm
  have hxlt : x < beta := by dsimp [x]; linarith
  have hnext : rotationPrefix alpha (n + 1) x ≠ rotationPrefix alpha (n + 1) y := by
    intro heq
    have hc := (hstep x hx01 y hy01).mp heq |>.2
    exact (not_le_of_gt hxlt) (hc.mpr le_rfl)
  refine ⟨hstep, j, ⟨hjlo, hjhi, x, y, hxab, hyab, hxlt, le_rfl, hxy, hnext⟩, ?_⟩
  intro k hk
  by_contra hkj
  have hd := rotation_gap_arcs_pairwise_disjoint alpha (n + 1)
    (Set.mem_univ k) (Set.mem_univ j) hkj
  exact (Set.disjoint_left.mp hd) (show beta ∈ rotationGapArc alpha (n + 1) k from
    ⟨hk.1.le, hk.2.1⟩) hj

#print axioms rotationPrefix
#print axioms rotation_prefix_cell_and_decoder
#print axioms rotation_prefix_single_cut

end D5.S1.Words.Mechanical.RotationObservationCells

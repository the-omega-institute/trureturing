/- GID: D5/S3/FiniteGroups/BajnokBeattyExtremalGrowth
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyExtremalGrowth
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Short-kernel Lee image counting by an upper-cap transversal. -/

import D5.S3.FiniteGroups.BajnokBeattySharpMaximum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Interval

/-!
proof_shape: lee_ball_image_card_of_short_kernel: content.
admission_basis: escape-witness.
escape_witness: trim_bijOn constructs a transversal by lowering precisely the
upper overlap cap once. Its injectivity and surjectivity feed finsetCard_eq,
then card_sdiff_add_card_eq_card, on the live path to the numerical formula.
The encoding, cap translation and norm adapters are consumed private helpers.
No literature novelty or current-publication priority is claimed.
-/

set_option autoImplicit false

universe u

namespace D5.S3.FiniteGroups.BajnokBeattyExtremalGrowth

open NearSquareLatticeRigidity
open scoped Classical

/-- The finite integer Lee diamond of natural radius `r`. -/
def leeDiamond (r : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(r : ℤ)) r) ×ˢ (Finset.Icc (-(r : ℤ)) r)).filter
    (fun z => |z.1| + |z.2| ≤ (r : ℤ))

private theorem mem_leeDiamond {r : ℕ} {z : ℤ × ℤ} :
    z ∈ leeDiamond r ↔ |z.1| + |z.2| ≤ (r : ℤ) := by
  simp only [leeDiamond, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact And.right
  · intro h
    have hx := abs_le.mp (show |z.1| ≤ (r : ℤ) by
      linarith [abs_nonneg z.2])
    have hy := abs_le.mp (show |z.2| ≤ (r : ℤ) by
      linarith [abs_nonneg z.1])
    exact ⟨⟨hx, hy⟩, h⟩

private def leeNorm (z : ℤ × ℤ) : ℤ := |z.1| + |z.2|

private theorem norm_sub_le (x y : ℤ × ℤ) :
    leeNorm (x - y) ≤ leeNorm x + leeNorm y := by
  dsimp [leeNorm]
  change |x.1-y.1| + |x.2-y.2| ≤ |x.1|+|x.2|+(|y.1|+|y.2|)
  linarith [abs_sub x.1 y.1, abs_sub x.2 y.2]

private def upperCap (B r : ℕ) : Finset (ℤ × ℤ) :=
  leeDiamond r ∩ (leeDiamond r).image (fun z => z+(0,2*(B : ℤ)))

private def trimmedDiamond (B r : ℕ) : Finset (ℤ × ℤ) :=
  leeDiamond r \ upperCap B r

private theorem mem_upperCap {B r : ℕ} {z : ℤ × ℤ} :
    z ∈ upperCap B r ↔ z ∈ leeDiamond r ∧
      z - (0, 2*(B : ℤ)) ∈ leeDiamond r := by
  simp only [upperCap, Finset.mem_inter, Finset.mem_image]
  constructor
  · rintro ⟨hz,w,hw,rfl⟩
    exact ⟨hz, by simpa using hw⟩
  · rintro ⟨hz,hzm⟩
    exact ⟨hz,z-(0,2*(B : ℤ)),hzm,sub_add_cancel _ _⟩

private theorem cap_lower_not_cap {B r : ℕ} (hBr : r < 2*B)
    {z : ℤ × ℤ} (hz : z ∈ upperCap B r) :
    z - (0,2*(B : ℤ)) ∉ upperCap B r := by
  intro hl
  have htop := mem_leeDiamond.mp (mem_upperCap.mp hz).1
  have hbottom := mem_leeDiamond.mp (mem_upperCap.mp hl).2
  have hd := norm_sub_le z ((z-(0,2*(B : ℤ)))-(0,2*(B : ℤ)))
  have he : z-((z-(0,2*(B : ℤ)))-(0,2*(B : ℤ))) = (0,4*(B : ℤ)) := by
    ext <;> simp <;> ring
  rw [he] at hd
  have hB : (0 : ℤ) ≤ 4*(B : ℤ) := by positivity
  simp only [leeNorm, abs_zero, zero_add, abs_of_nonneg hB] at hd
  change |z.1-0-0| + |z.2-2*(B : ℤ)-2*(B : ℤ)| ≤ (r : ℤ) at hbottom
  dsimp [leeNorm] at hd
  have hBrZ : (r : ℤ) < 2*(B : ℤ) := by exact_mod_cast hBr
  linarith

/-- The new fiber argument. It is private because its actual consumer is the
cardinality theorem, not a separate transversal endpoint. -/
private theorem trim_bijOn {G : Type u} [AddCommGroup G]
    (f : (ℤ × ℤ) →+ G) {B r : ℕ} (hBr : r < 2*B)
    (hh : f (0,2*(B : ℤ)) = 0)
    (hshort : ∀ z : ℤ × ℤ, |z.1|+|z.2| ≤ 2*(r : ℤ) → f z = 0 →
      z = 0 ∨ z = (0,2*(B : ℤ)) ∨ z = (0,-2*(B : ℤ))) :
    Set.BijOn f (↑(trimmedDiamond B r) : Set (ℤ × ℤ))
      (↑((leeDiamond r).image f) : Set G) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact Finset.mem_image.mpr ⟨z, (Finset.mem_sdiff.mp hz).1, rfl⟩
  · intro x hx y hy he
    obtain ⟨hxD,hxC⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hyD,hyC⟩ := Finset.mem_sdiff.mp hy
    have hnorm : |(x-y).1|+|(x-y).2| ≤ 2*(r : ℤ) := by
      have ht := norm_sub_le x y
      have h1 := mem_leeDiamond.mp hxD
      have h2 := mem_leeDiamond.mp hyD
      dsimp [leeNorm] at ht
      linarith
    have hzero : f (x-y) = 0 := by rw [map_sub, he, sub_self]
    rcases hshort (x-y) hnorm hzero with h0 | hp | hn
    · exact sub_eq_zero.mp h0
    · exact False.elim (hxC (mem_upperCap.mpr ⟨hxD, by
        have hxy : x-(0,2*(B : ℤ)) = y := by rw [← hp]; abel
        simpa only [hxy] using hyD⟩))
    · exact False.elim (hyC (mem_upperCap.mpr ⟨hyD, by
        have hyx : y-(0,2*(B : ℤ)) = x := by
          have hn' : x-y = -(0,2*(B : ℤ)) := by simpa using hn
          have hp' := congrArg Neg.neg hn'
          have hp'' : y-x = (0,2*(B : ℤ)) := by simpa using hp'
          rw [← hp'']; abel
        simpa only [hyx] using hxD⟩))
  · intro g hg
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hg
    by_cases hcap : z ∈ upperCap B r
    · refine ⟨z-(0,2*(B : ℤ)), Finset.mem_sdiff.mpr
        ⟨(mem_upperCap.mp hcap).2, cap_lower_not_cap hBr hcap⟩, ?_⟩
      rw [map_sub, hh, sub_zero]
    · exact ⟨z, Finset.mem_sdiff.mpr ⟨hz,hcap⟩, rfl⟩

private def decodePair (r : ℕ) (c : LeeSquareCompression.LeeCode r) : ℤ × ℤ :=
  (LeeSquareCompression.decodeLee r c 0, LeeSquareCompression.decodeLee r c 1)

private theorem decodePair_mem (r : ℕ) (c : LeeSquareCompression.LeeCode r) :
    decodePair r c ∈ leeDiamond r := by
  apply mem_leeDiamond.mpr
  rcases c with ⟨a,b⟩ | ⟨a,b⟩
  all_goals
    have ha := a.isLt
    have hb := b.isLt
    dsimp [decodePair, LeeSquareCompression.decodeLee]
    apply (LeeSquareCompression.lee_iff_square _ _ _).mpr
    constructor <;> rw [abs_le] <;> omega

private theorem decodePair_injective (r : ℕ) : Function.Injective (decodePair r) := by
  intro c d he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  rcases c with ⟨a,b⟩ | ⟨a,b⟩ <;> rcases d with ⟨c,d⟩ | ⟨c,d⟩
  all_goals dsimp [decodePair, LeeSquareCompression.decodeLee] at hx hy
  · have hac : a = c := Fin.ext (by omega)
    have hbd : b = d := Fin.ext (by omega)
    subst c; subst d; rfl
  · omega
  · omega
  · have hac : a = c := Fin.ext (by omega)
    have hbd : b = d := Fin.ext (by omega)
    subst c; subst d; rfl

private theorem leeDiamond_card (r : ℕ) :
    (leeDiamond r).card = 2*r^2+2*r+1 := by
  classical
  have hbij : Set.BijOn (decodePair r)
      (↑(Finset.univ : Finset (LeeSquareCompression.LeeCode r)) :
        Set (LeeSquareCompression.LeeCode r)) (↑(leeDiamond r) : Set (ℤ × ℤ)) := by
    refine ⟨fun c _ => decodePair_mem r c,
      fun c _ d _ he => decodePair_injective r he, ?_⟩
    intro z hz
    obtain ⟨c,hc⟩ := LeeSquareCompression.leeCode_complete
      (z := ![z.1,z.2]) (mem_leeDiamond.mp hz)
    refine ⟨c, Finset.mem_univ _, ?_⟩
    exact Prod.ext (congrFun hc 0) (congrFun hc 1)
  have hcard := Set.BijOn.finsetCard_eq (decodePair r) hbij
  have hcode : Fintype.card (LeeSquareCompression.LeeCode r) = (r+1)^2+r^2 := by
    simp [LeeSquareCompression.LeeCode, Fintype.card_sum, Fintype.card_prod, pow_two]
  rw [Finset.card_univ, hcode] at hcard
  nlinarith

private theorem cap_empty {B r : ℕ} (hr : r < B) : upperCap B r = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro z hz
  obtain ⟨h1,h2⟩ := mem_upperCap.mp hz
  have h1' := mem_leeDiamond.mp h1
  have h2' := mem_leeDiamond.mp h2
  have hd := abs_sub z.2 (z.2-2*(B : ℤ))
  have he : z.2-(z.2-2*(B : ℤ)) = 2*(B : ℤ) := by ring
  rw [he, abs_of_nonneg (by positivity)] at hd
  change |z.1-0|+|z.2-2*(B : ℤ)| ≤ (r : ℤ) at h2'
  have hrZ : (r : ℤ) < (B : ℤ) := by exact_mod_cast hr
  simp only [sub_zero] at h2'
  linarith [abs_nonneg z.1]

private theorem cap_translate {B r : ℕ} (hBr : B ≤ r) :
    upperCap B r = (leeDiamond (r-B)).image (fun z => z+(0,(B : ℤ))) := by
  ext z
  have hcast : ((r-B : ℕ) : ℤ) = (r : ℤ)-(B : ℤ) := by omega
  have habs : ∀ y : ℤ, max |y| |y-2*(B : ℤ)| = (B : ℤ)+|y-(B : ℤ)| := by
    intro y
    rw [max_def]
    split_ifs
    all_goals
      rcases le_total 0 y with hy | hy <;>
        rcases le_total 0 (y-2*(B : ℤ)) with hy2 | hy2 <;>
        rcases le_total 0 (y-(B : ℤ)) with hy1 | hy1
      all_goals simp only [abs_of_nonneg, abs_of_nonpos, hy, hy2, hy1] at *
      all_goals omega
  have hm : (z ∈ upperCap B r) ↔
      z-(0,(B : ℤ)) ∈ leeDiamond (r-B) := by
    simp only [mem_upperCap, mem_leeDiamond, Prod.fst_sub, Prod.snd_sub,
      sub_zero, hcast]
    have ht := habs z.2
    rw [max_def] at ht
    split_ifs at ht <;> omega
  rw [hm, Finset.mem_image]
  constructor
  · intro hz
    exact ⟨z-(0,(B : ℤ)), hz, sub_add_cancel _ _⟩
  · rintro ⟨w,hw,rfl⟩
    simpa using hw

/-- For any additive commutative group, the short-kernel hypothesis determines
the finite Lee image exactly. Neither finiteness of `G` nor surjectivity of `f`
is assumed. The natural radius condition `r < 2*B` is essential. -/
theorem lee_ball_image_card_of_short_kernel {G : Type u} [AddCommGroup G]
    (f : (ℤ × ℤ) →+ G) {B r : ℕ} (hB : 0 < B) (hBr : r < 2*B)
    (hh : f (0,2*(B : ℤ)) = 0)
    (hshort : ∀ z : ℤ × ℤ, |z.1|+|z.2| ≤ 2*(r : ℤ) → f z = 0 →
      z = 0 ∨ z = (0,2*(B : ℤ)) ∨ z = (0,-2*(B : ℤ))) :
    ((leeDiamond r).image f).card =
      if r < B then 2*r^2+2*r+1 else 2*B*(2*r-B+1) := by
  classical
  have hbij := trim_bijOn f hBr hh hshort
  have hcard := Set.BijOn.finsetCard_eq f hbij
  have hsub : upperCap B r ⊆ leeDiamond r := by
    intro z hz
    exact (mem_upperCap.mp hz).1
  have hbalance := Finset.card_sdiff_add_card_eq_card hsub
  change (trimmedDiamond B r).card + (upperCap B r).card =
    (leeDiamond r).card at hbalance
  rw [hcard, leeDiamond_card] at hbalance
  by_cases hr : r < B
  · rw [cap_empty hr, Finset.card_empty, add_zero] at hbalance
    simpa only [if_pos hr] using hbalance
  · have hBr' : B ≤ r := by omega
    rw [if_neg hr]
    have hcap : (upperCap B r).card = 2*(r-B)^2+2*(r-B)+1 := by
      rw [cap_translate hBr', Finset.card_image_of_injective _
        (fun x y h => add_right_cancel h),
        leeDiamond_card]
    rw [hcap] at hbalance
    have hsplit : r = (r-B)+B := by omega
    have hpoly : 2*r^2+2*r+1 =
        2*B*(2*r-B+1) + (2*(r-B)^2+2*(r-B)+1) := by
      have hdiff : 2*r-B = 2*(r-B)+B := by omega
      rw [hdiff]
      calc
        2*r^2+2*r+1 = 2*((r-B)+B)^2+2*((r-B)+B)+1 := by
          conv_lhs => rw [hsplit]
        _ = 2*B*(2*(r-B)+B+1)+(2*(r-B)^2+2*(r-B)+1) := by ring
    omega

end D5.S3.FiniteGroups.BajnokBeattyExtremalGrowth

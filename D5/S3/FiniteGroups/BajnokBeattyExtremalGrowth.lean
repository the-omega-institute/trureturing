/- GID: D5/S3/FiniteGroups/BajnokBeattyExtremalGrowth
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyExtremalGrowth
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Short-kernel Lee image counting by an upper-cap transversal. -/

import D5.S3.FiniteGroups.BajnokBeattySharpMaximum

/-!
proof_shape: lee_ball_image_card_of_short_kernel, sharp_pair_growth: content.
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
      change |x.1-y.1|+|x.2-y.2| ≤ 2*(r : ℤ)
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
  apply Finset.eq_empty_iff_forall_notMem.mpr
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
    split_ifs with hmax
    all_goals
      rcases le_total 0 y with hy | hy <;>
        rcases le_total 0 (y-2*(B : ℤ)) with hy2 | hy2 <;>
        rcases le_total 0 (y-(B : ℤ)) with hy1 | hy1
      all_goals simp only [abs_of_nonneg, abs_of_nonpos, hy, hy2, hy1] at hmax ⊢
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

open NearSquareLatticeRigidity BajnokBeattyCayleyNecessity
open scoped Classical

private def pairHom : Plane →+ (ℤ × ℤ) where
  toFun z := (z 0,z 1)
  map_zero' := rfl
  map_add' _ _ := rfl

private def coefficientHom {G : Type u} [AddCommGroup G] (a b : G) : (ℤ × ℤ) →+ G where
  toFun z := z.1 • a + z.2 • b
  map_zero' := by simp
  map_add' z w := by
    change (z.1+w.1) • a+(z.2+w.2) • b =
      (z.1 • a+z.2 • b)+(w.1 • a+w.2 • b)
    simp only [add_zsmul]
    abel

private def compressedKernel {G : Type u} [AddCommGroup G]
    (f : Plane →+ G) (p : ℕ) : Submodule ℤ Plane :=
  (f.toIntLinearMap.ker.map sumDiff).comap (LeeSquareCompression.dilation (p : ℤ))

/-- Preserve the SAME Smith divisor and its coordinate containment, then
force it to be the least prime factor by equality of the actual order. -/
private theorem sharp_compressed_kernel {G : Type u} [AddCommGroup G] [Finite G]
    {s t : ℕ} (hs : 3 ≤ s) (hcomposite : ¬ Nat.Prime (2*s+1))
    (ht : 1 ≤ t)
    (hsize : Nat.minFac (2*s+1)*(2*t+1) = 2*s+1)
    (hnoncyclic : ¬ IsAddCyclic G) (f : Plane →+ G) (hf : Function.Surjective f)
    (hcover : ∀ z : Plane, ∃ w : Plane,
      |w 0|+|w 1| ≤ (s : ℤ) ∧ z-w ∈ f.toIntLinearMap.ker)
    (horder : Nat.card G = BajnokBeattySharpMaximum.MaximumOrder s) :
    (∀ z ∈ f.toIntLinearMap.ker,
      (Nat.minFac (2*s+1) : ℤ) ∣ z 0 ∧ (Nat.minFac (2*s+1) : ℤ) ∣ z 1) ∧
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      compressedKernel f (Nat.minFac (2*s+1)) =
        Submodule.span ℤ (Set.range
          ![![(2*(t : ℤ)+1), -ε], ![-1, ε*(2*(t : ℤ)+1)]]) := by
  let p : ℕ := Nat.minFac (2*s+1)
  let K := f.toIntLinearMap.ker
  let M := K.map sumDiff
  let L := M.comap (LeeSquareCompression.dilation (p : ℤ))
  have hindex : K.toAddSubgroup.index = Nat.card G := by
    change Nat.card (Plane ⧸ K) = Nat.card G
    exact Nat.card_congr (f.toIntLinearMap.quotKerEquivOfSurjective hf).toEquiv
  obtain ⟨_,hp3,_⟩ := BajnokBeattySharpMaximum.minFac_parameters s hs hcomposite
  change 3 ≤ p at hp3
  have hpsmall : p^2 ≤ 2*s+1 :=
    Nat.minFac_sq_le_self (by omega) hcomposite
  have htwice : 2*Nat.card G+p^2 = (2*s+1)^2 := by
    have harith := (BajnokBeattySharpMaximum.composite_arithmetic s hs hcomposite).1
    rw [horder, BajnokBeattySharpMaximum.MaximumOrder, if_neg hcomposite]
    change 2*(2*s^2+2*s-(p^2-1)/2)+p^2 = (2*s+1)^2
    change 2*(2*s^2+2*s-(p^2-1)/2) = (2*s+1)^2-p^2 at harith
    have : p^2 ≤ (2*s+1)^2 := by nlinarith
    omega
  have hN : 2*(Nat.card G : ℤ)+(p : ℤ)^2 = (2*(s : ℤ)+1)^2 := by
    exact_mod_cast htwice
  have hpZ : (p : ℤ)^2 ≤ 2*(s : ℤ)+1 := by exact_mod_cast hpsmall
  have hlarge : 2*(s : ℤ)^2 < (K.toAddSubgroup.index : ℤ) := by
    rw [hindex]
    have hsZ : (3 : ℤ) ≤ s := by exact_mod_cast hs
    nlinarith
  obtain ⟨c,hc,hcdiv⟩ := BajnokBeattyFiniteUpper.kernel_common_divisor hnoncyclic f hf
  have hlat := LeeSquareCompression.lattice_upper_bound K
    (c := (c : ℤ)) (s := (s : ℤ)) (by exact_mod_cast hc)
    (by exact_mod_cast hs) hcdiv hcover
  rcases hlat with hlow | ⟨hcodd,hcdvd,hbound⟩
  · omega
  have hpc : p ≤ c := Nat.minFac_le_of_dvd hc (by exact_mod_cast hcdvd)
  have hceq : c = p := by
    rw [hindex] at hbound
    have hcZ : (2 : ℤ) ≤ c := by exact_mod_cast hc
    have hpZ' : (p : ℤ) ≤ c := by exact_mod_cast hpc
    have hcp : (c : ℤ) = p := by nlinarith
    exact_mod_cast hcp
  subst c
  refine ⟨hcdiv, ?_⟩
  have hMdiv : ∀ z ∈ M, (p : ℤ) ∣ z 0 ∧ (p : ℤ) ∣ z 1 := by
    rintro z ⟨w,hw,rfl⟩
    exact ⟨(hcdiv w hw).1.add (hcdiv w hw).2,
      (hcdiv w hw).1.sub (hcdiv w hw).2⟩
  have hsquare := LeeSquareCompression.large_index_square_lift K
    (c := (p : ℤ)) (s := (s : ℤ)) (by exact_mod_cast hp3) hcodd
    (by exact_mod_cast hs) hcdiv hcover hlarge
  have hsizeZ : (p : ℤ)*(2*(t : ℤ)+1) = 2*(s : ℤ)+1 := by exact_mod_cast hsize
  have hquot : (2*(s : ℤ)+1)/(p : ℤ) = 2*(t : ℤ)+1 :=
    Int.ediv_eq_of_eq_mul_right (by omega) hsizeZ.symm
  have hrect : RectangleCovers L (2*(t : ℤ)+1) (2*(t : ℤ)+1) := by
    have hr := LeeSquareCompression.residue_rectangle M
      (c := (p : ℤ)) (s := (s : ℤ)) (by omega) hMdiv (fun z => hsquare _)
    simpa only [hquot] using hr
  have hscale := congrArg (fun n : ℕ => (n : ℤ))
    (LeeSquareCompression.scaled_index M (c := (p : ℤ)) (by omega) hMdiv)
  have hmap := congrArg (fun n : ℕ => (n : ℤ))
    (LeeSquareCompression.mapped_index K)
  have hscale' : (M.toAddSubgroup.index : ℤ) =
      (L.toAddSubgroup.index : ℤ)*(p : ℤ)^2 := by
    simpa [L, Int.natCast_natAbs, abs_of_pos (show (0 : ℤ) < p by omega)] using hscale
  have hmap' : (M.toAddSubgroup.index : ℤ) = 2*(Nat.card G : ℤ) := by
    simpa [M,hindex,Nat.cast_mul,mul_comm] using hmap
  have hmul : (L.toAddSubgroup.index : ℤ)*(p : ℤ)^2 =
      ((2*(t : ℤ)+1)^2-1)*(p : ℤ)^2 := by
    have hn := congrArg (fun z : ℤ => z^2) hsizeZ
    nlinarith only [hscale',hmap',hN,hn]
  have hLindex : (L.toAddSubgroup.index : ℤ) = (2*(t : ℤ)+1)^2-1 :=
    mul_right_cancel₀ (by positivity : (p : ℤ)^2 ≠ 0) hmul
  obtain ⟨a,b,ε,ha,ham,hb,hbm,hε,hab,hL⟩ :=
    near_square_rigidity L (n := 2*(t : ℤ)+1) (δ := 1)
      (by omega) (by norm_num) (by omega) hLindex hrect
  have ha1 : 1 ≤ a := by
    by_contra hn
    have ha0 : a = 0 := by omega
    simp [ha0] at hab
  have hb1 : 1 ≤ b := by
    by_contra hn
    have hb0 : b = 0 := by omega
    simp [hb0] at hab
  have haeq : a = 1 := by
    nlinarith only [ha1, hab, mul_le_mul_of_nonneg_left hb1 ha]
  have hbeq : b = 1 := by simpa only [haeq, one_mul] using hab
  refine ⟨ε,hε,?_⟩
  simpa only [compressedKernel, K, M, L, haeq,hbeq,mul_one,neg_one_mul] using hL

/-- A vector in the canonical diagonal lattice has coordinates
`(A(u-v),B(u+v))`. This is a consumed short-vector estimate, not a kernel API. -/
private theorem diagonal_short {A B s : ℤ} (hA : 0 < A) (hB : 0 < B)
    (hsum : 2*s < A+B) (h2A : 2*s < 2*A) (h4B : 2*s < 4*B)
    (u v : ℤ) (hz : |A*(u-v)|+|B*(u+v)| ≤ 2*s) :
    (A*(u-v),B*(u+v)) = 0 ∨
      (A*(u-v),B*(u+v)) = (0,2*B) ∨
      (A*(u-v),B*(u+v)) = (0,-2*B) := by
  have hzero : u-v = 0 := by
    by_contra hm
    have hm1 : 1 ≤ |u-v| := by
      have hn := abs_nonneg (u-v)
      have hne : |u-v| ≠ 0 := abs_ne_zero.mpr hm
      omega
    by_cases hd : u+v = 0
    · have hm2 : 2 ≤ |u-v| := by
        rcases le_total 0 (u-v) with h | h
        · rw [abs_of_nonneg h]; omega
        · rw [abs_of_nonpos h]; omega
      rw [abs_mul,abs_mul,abs_of_pos hA,abs_of_pos hB] at hz
      nlinarith [mul_le_mul_of_nonneg_left hm2 (le_of_lt hA),
        mul_nonneg (le_of_lt hB) (abs_nonneg (u+v))]
    · have hd1 : 1 ≤ |u+v| := by
        have hn := abs_nonneg (u+v)
        have hne : |u+v| ≠ 0 := abs_ne_zero.mpr hd
        omega
      rw [abs_mul,abs_mul,abs_of_pos hA,abs_of_pos hB] at hz
      nlinarith [mul_le_mul_of_nonneg_left hm1 (le_of_lt hA),
        mul_le_mul_of_nonneg_left hd1 (le_of_lt hB)]
  have huv : u = v := by omega
  subst v
  have hu : -1 ≤ u ∧ u ≤ 1 := by
    have hh : |2*B*u| ≤ 2*s := by
      have he : B*(u+u) = 2*B*u := by ring
      simpa only [sub_self,mul_zero,abs_zero,zero_add,he] using hz
    have hh' := abs_le.mp hh
    constructor
    · by_contra hn
      have hu2 : u ≤ -2 := by omega
      have hm := mul_le_mul_of_nonneg_left hu2 (show 0 ≤ 2*B by positivity)
      nlinarith
    · by_contra hn
      have hu2 : 2 ≤ u := by omega
      have hm := mul_le_mul_of_nonneg_left hu2 (show 0 ≤ 2*B by positivity)
      nlinarith
  have hu3 : u = 0 ∨ u = 1 ∨ u = -1 := by omega
  rcases hu3 with rfl | rfl | rfl
  · left; ext <;> simp
  · right; left; ext <;> simp <;> ring
  · right; right; ext <;> simp <;> ring

/-- Lift a compressed vector through the ORIGINAL S-image. This uses its
membership witness, not a discarded abstract lattice isomorphism. -/
private theorem compressed_preimage_mem {G : Type u} [AddCommGroup G]
    (f : Plane →+ G) (p : ℕ) {w z : Plane}
    (hw : w ∈ compressedKernel f p)
    (hz : sumDiff z = (p : ℤ) • w) : z ∈ f.toIntLinearMap.ker := by
  change (p : ℤ) • w ∈ f.toIntLinearMap.ker.map sumDiff at hw
  obtain ⟨k,hk,hke⟩ := hw
  have he : k = z := sumDiff_injective (hke.trans hz.symm)
  change f k = 0 at hk
  change f z = 0
  rwa [he] at hk

/-- The finite-index classification is consumed solely to discharge the
short-kernel premise of the general cap-transversal count. -/
private theorem short_relations_of_rigidity {G : Type u} [AddCommGroup G]
    (f : Plane →+ G) {p t s : ℕ} (hp : 3 ≤ p) (ht : 1 ≤ t)
    (hsize : p*(2*t+1) = 2*s+1)
    (hdiv : ∀ z ∈ f.toIntLinearMap.ker, (p : ℤ) ∣ z 0 ∧ (p : ℤ) ∣ z 1)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hL : compressedKernel f p = Submodule.span ℤ (Set.range
      ![![(2*(t : ℤ)+1),-ε], ![-1,ε*(2*(t : ℤ)+1)]])) :
    (f ![0,2*(p : ℤ)*t] = 0 ∧
      ∀ z : Plane, |z 0|+|z 1| ≤ 2*(s : ℤ) → f z = 0 →
        z = 0 ∨ z = ![0,2*(p : ℤ)*t] ∨ z = ![0,-2*(p : ℤ)*t]) ∨
    (f ![2*(p : ℤ)*t,0] = 0 ∧
      ∀ z : Plane, |z 0|+|z 1| ≤ 2*(s : ℤ) → f z = 0 →
        z = 0 ∨ z = ![2*(p : ℤ)*t,0] ∨ z = ![-2*(p : ℤ)*t,0]) := by
  let A : ℤ := (p : ℤ)*(t+1)
  let B : ℤ := (p : ℤ)*t
  have hpZ : (3 : ℤ) ≤ p := by exact_mod_cast hp
  have htZ : (1 : ℤ) ≤ t := by exact_mod_cast ht
  have hsizeZ : (p : ℤ)*(2*(t : ℤ)+1) = 2*(s : ℤ)+1 := by exact_mod_cast hsize
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hsum : A+B = 2*(s : ℤ)+1 := by dsimp [A,B]; nlinarith
  have hdiff : A-B = p := by dsimp [A,B]; ring
  have h4B : 2*(s : ℤ) < 4*B := by
    have hpt : (p : ℤ) ≤ (p : ℤ)*t := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left htZ (show (0 : ℤ) ≤ p by omega)
    dsimp [B]
    nlinarith
  have h2A : 2*(s : ℤ) < 2*A := by nlinarith
  have hu : ![2*(t : ℤ)+1,-ε] ∈ compressedKernel f p := by
    rw [hL]
    exact Submodule.subset_span ⟨0,rfl⟩
  have hv : ![-1,ε*(2*(t : ℤ)+1)] ∈ compressedKernel f p := by
    rw [hL]
    exact Submodule.subset_span ⟨1,rfl⟩
  have hsum_mem := (compressedKernel f p).add_mem hu hv
  have hcoordinates : ∀ z ∈ f.toIntLinearMap.ker, ∃ u v : ℤ,
      (ε = -1 ∧ z = ![A*(u-v),B*(u+v)]) ∨
      (ε = 1 ∧ z = ![B*(u+v),A*(u-v)]) := by
    intro z hz
    obtain ⟨⟨x,hx⟩,⟨y,hy⟩⟩ := hdiv z hz
    have he : z = (p : ℤ) • (![x,y] : Plane) := by
      ext i
      fin_cases i <;> simp [hx,hy]
    have hw : sumDiff ![x,y] ∈ compressedKernel f p := by
      change (p : ℤ) • sumDiff ![x,y] ∈ f.toIntLinearMap.ker.map sumDiff
      refine ⟨z,hz,?_⟩
      rw [he,map_smul]
    rw [hL,Matrix.range_cons_cons_empty,Submodule.mem_span_pair] at hw
    obtain ⟨u,v,hw⟩ := hw
    have h0 := congrFun hw 0
    have h1 := congrFun hw 1
    change u*(2*(t : ℤ)+1)+v*(-1) = x+y at h0
    change u*(-ε)+v*(ε*(2*(t : ℤ)+1)) = x-y at h1
    refine ⟨u,v,?_⟩
    rcases hε with hε | hε
    · right
      refine ⟨hε,?_⟩
      have hx' : x = (t : ℤ)*(u+v) := by
        simp only [hε] at h1
        nlinarith only [h0, h1]
      have hy' : y = ((t : ℤ)+1)*(u-v) := by
        simp only [hε] at h1
        nlinarith only [h0, h1]
      rw [he,hx',hy']
      ext i
      fin_cases i <;> simp [A,B] <;> ring
    · left
      refine ⟨hε,?_⟩
      have hx' : x = ((t : ℤ)+1)*(u-v) := by
        simp only [hε] at h1
        nlinarith only [h0, h1]
      have hy' : y = (t : ℤ)*(u+v) := by
        simp only [hε] at h1
        nlinarith only [h0, h1]
      rw [he,hx',hy']
      ext i
      fin_cases i <;> simp [A,B] <;> ring
  rcases hε with hε | hε
  · right
    constructor
    · apply compressed_preimage_mem f p hsum_mem
      ext i
      fin_cases i <;> simp [sumDiff,hε] <;> ring
    · intro z hz hzero
      obtain ⟨u,v,hcanonical | hswapped⟩ := hcoordinates z hzero
      · omega
      · have hz' : |A*(u-v)|+|B*(u+v)| ≤ 2*(s : ℤ) := by
          simpa [hswapped.2,add_comm] using hz
        have hd := diagonal_short hA hB (by omega) h2A h4B u v hz'
        rcases hd with hd | hd | hd
        · left
          simpa [hswapped.2] using
            congrArg (fun q : ℤ × ℤ => (![q.2,q.1] : Plane)) hd
        · right; left
          simpa [hswapped.2,B,mul_assoc] using
            congrArg (fun q : ℤ × ℤ => (![q.2,q.1] : Plane)) hd
        · right; right
          simpa [hswapped.2,B,mul_assoc] using
            congrArg (fun q : ℤ × ℤ => (![q.2,q.1] : Plane)) hd
  · left
    constructor
    · apply compressed_preimage_mem f p hsum_mem
      ext i
      fin_cases i <;> simp [sumDiff,hε] <;> ring
    · intro z hz hzero
      obtain ⟨u,v,hcanonical | hswapped⟩ := hcoordinates z hzero
      · have hz' : |A*(u-v)|+|B*(u+v)| ≤ 2*(s : ℤ) := by
          simpa [hcanonical.2] using hz
        have hd := diagonal_short hA hB (by omega) h2A h4B u v hz'
        rcases hd with hd | hd | hd
        · left
          simpa [hcanonical.2] using
            congrArg (fun q : ℤ × ℤ => (![q.1,q.2] : Plane)) hd
        · right; left
          simpa [hcanonical.2,B,mul_assoc] using
            congrArg (fun q : ℤ × ℤ => (![q.1,q.2] : Plane)) hd
        · right; right
          simpa [hcanonical.2,B,mul_assoc] using
            congrArg (fun q : ℤ × ℤ => (![q.1,q.2] : Plane)) hd
      · omega

private theorem swapped_image_card {G : Type u} [AddCommGroup G]
    (f : (ℤ × ℤ) →+ G) (r : ℕ) :
    ((leeDiamond r).image (f.comp (AddEquiv.prodComm : (ℤ × ℤ) ≃+ (ℤ × ℤ)).toAddMonoidHom)).card =
      ((leeDiamond r).image f).card := by
  congr 1
  ext g
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨(z.2,z.1), mem_leeDiamond.mpr (by
      simpa [add_comm] using mem_leeDiamond.mp hz), rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨(z.2,z.1), mem_leeDiamond.mpr (by
      simpa [add_comm] using mem_leeDiamond.mp hz), rfl⟩

/-- Every actual finite noncyclic maximum pair at a composite odd boundary has
the same signed ball growth, throughout the ORIGINAL range `r ≤ s`.
The factor `t` is only the odd-cofactor parameter, supplied by the existing
minFac_parameters theorem; no classification or isomorphism is exported. -/
private theorem sharp_pair_growth_with_cofactor {G : Type u} [AddCommGroup G] [Finite G]
    {s t : ℕ} (hs : 3 ≤ s) (hcomposite : ¬ Nat.Prime (2*s+1))
    (ht : 1 ≤ t) (hsize : Nat.minFac (2*s+1)*(2*t+1) = 2*s+1)
    (hnoncyclic : ¬ IsAddCyclic G) (a b : G) (_hab : a ≠ b)
    (hcover : ∀ g : G, ∃ x y : ℤ,
      |x|+|y| ≤ (s : ℤ) ∧ x • a+y • b = g)
    (horder : Nat.card G = BajnokBeattySharpMaximum.MaximumOrder s)
    (r : ℕ) (hr : r ≤ s) :
    let B := Nat.minFac (2*s+1)*t
    ((leeDiamond r).image (fun z => z.1 • a+z.2 • b)).card =
      if r < B then 2*r^2+2*r+1 else 2*B*(2*r-B+1) := by
  let p : ℕ := Nat.minFac (2*s+1)
  let B : ℕ := p*t
  let f := coefficientHom a b
  let F := f.comp pairHom
  have hf : Function.Surjective F := by
    intro g
    obtain ⟨x,y,_,he⟩ := hcover g
    exact ⟨![x,y],he⟩
  have hKcover : ∀ z : Plane, ∃ w : Plane,
      |w 0|+|w 1| ≤ (s : ℤ) ∧ z-w ∈ F.toIntLinearMap.ker := by
    intro z
    obtain ⟨x,y,hxy,he⟩ := hcover (F z)
    refine ⟨![x,y],hxy,?_⟩
    change F (z-![x,y]) = 0
    rw [map_sub]
    change F z-(x • a+y • b) = 0
    rw [he,sub_self]
  obtain ⟨hdiv,ε,hε,hL⟩ := sharp_compressed_kernel hs hcomposite ht hsize
    hnoncyclic F hf hKcover horder
  obtain ⟨_,hp3,_⟩ := BajnokBeattySharpMaximum.minFac_parameters s hs hcomposite
  have hBp : 0 < B := by dsimp [B,p]; positivity
  have hsB : s < 2*B := by
    have hpZ : (3 : ℤ) ≤ p := by exact_mod_cast hp3
    have htZ : (1 : ℤ) ≤ t := by exact_mod_cast ht
    have hsizeZ : (p : ℤ)*(2*(t : ℤ)+1) = 2*(s : ℤ)+1 := by exact_mod_cast hsize
    have hpt : (p : ℤ) ≤ (p : ℤ)*t := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left htZ (show (0 : ℤ) ≤ p by omega)
    have hz : (s : ℤ) < 2*(p : ℤ)*t := by nlinarith
    change s < 2*(p*t)
    have hn : s < 2*p*t := by exact_mod_cast hz
    simpa only [mul_assoc] using hn
  have hrB : r < 2*B := lt_of_le_of_lt hr hsB
  have hrZ : (r : ℤ) ≤ s := by exact_mod_cast hr
  change ((leeDiamond r).image f).card =
    if r < B then 2*r^2+2*r+1 else 2*B*(2*r-B+1)
  rcases short_relations_of_rigidity F hp3 ht hsize hdiv ε hε hL with hv | hh
  · apply lee_ball_image_card_of_short_kernel f hBp hrB
    · simpa [F,f,pairHom,B,Nat.cast_mul,mul_assoc] using hv.1
    · intro z hz hzero
      have hz' : |z.1|+|z.2| ≤ 2*(s : ℤ) := by omega
      have h := hv.2 ![z.1,z.2] hz' hzero
      rcases h with h | h | h
      · left
        exact Prod.ext (congrFun h 0) (congrFun h 1)
      · right; left
        simpa [pairHom,B,p,Nat.cast_mul,mul_assoc] using congrArg pairHom h
      · right; right
        simpa [pairHom,B,p,Nat.cast_mul,mul_assoc] using congrArg pairHom h
  · rw [← swapped_image_card f r]
    apply lee_ball_image_card_of_short_kernel
      (f.comp (AddEquiv.prodComm : (ℤ × ℤ) ≃+ (ℤ × ℤ)).toAddMonoidHom) hBp hrB
    · simpa [F,f,pairHom,B,Nat.cast_mul,mul_assoc] using hh.1
    · intro z hz hzero
      have hz' : |z.2|+|z.1| ≤ 2*(s : ℤ) := by linarith
      have h := hh.2 ![z.2,z.1] hz' hzero
      rcases h with h | h | h
      · left
        exact Prod.ext (congrFun h 1) (congrFun h 0)
      · right; left
        simpa [B,p,Nat.cast_mul,mul_assoc] using
          congrArg (fun w : Plane => (w 1,w 0)) h
      · right; right
        simpa [B,p,Nat.cast_mul,mul_assoc] using
          congrArg (fun w : Plane => (w 1,w 0)) h

/-- Exact ball growth for every actual composite maximum pair, with the
transition radius determined by the least prime factor of `2*s+1`. -/
theorem sharp_pair_growth {G : Type u} [AddCommGroup G] [Finite G]
    {s : ℕ} (hs : 3 ≤ s) (hcomposite : ¬ Nat.Prime (2*s+1))
    (hnoncyclic : ¬ IsAddCyclic G) (a b : G) (hab : a ≠ b)
    (hcover : ∀ g : G, ∃ x y : ℤ,
      |x|+|y| ≤ (s : ℤ) ∧ x • a+y • b = g)
    (horder : Nat.card G = BajnokBeattySharpMaximum.MaximumOrder s)
    (r : ℕ) (hr : r ≤ s) :
    let B := (2*s+1-Nat.minFac (2*s+1))/2
    ((leeDiamond r).image (fun z => z.1 • a+z.2 • b)).card =
      if r < B then 2*r^2+2*r+1 else 2*B*(2*r-B+1) := by
  obtain ⟨_,_,t,ht,hsize⟩ :=
    BajnokBeattySharpMaximum.minFac_parameters s hs hcomposite
  have hB : (2*s+1-Nat.minFac (2*s+1))/2 = Nat.minFac (2*s+1)*t := by
    have he : Nat.minFac (2*s+1)*(2*t+1) =
        2*(Nat.minFac (2*s+1)*t)+Nat.minFac (2*s+1) := by ring
    omega
  dsimp only
  rw [hB]
  exact sharp_pair_growth_with_cofactor hs hcomposite ht hsize
    hnoncyclic a b hab hcover horder r hr

end D5.S3.FiniteGroups.BajnokBeattyExtremalGrowth

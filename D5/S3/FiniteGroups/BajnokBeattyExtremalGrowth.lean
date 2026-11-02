/- GID: D5/S3/FiniteGroups/BajnokBeattyExtremalGrowth
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyExtremalGrowth
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Rank-one Lee image counting by a finite-fiber transversal. -/

import D5.S3.FiniteGroups.BajnokBeattySharpMaximum
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Finset.Max

/-!
proof_shape: lee_ball_image_card_of_displacement, sharp_pair_growth: content.
lee_ball_image_card_of_short_kernel: bind-only, consumed by
sharp_pair_growth_with_cofactor on the live path to sharp_pair_growth.
admission_basis: escape-witness.
escape_witness: trim_bijOn retains the bottom of each finite rank-one fiber.
A minimum of the dot product with h exists by Finset.exists_min_image;
subtracting h strictly lowers it. Integer Lee-norm interpolation forces any
other fiber point into the oriented cap. The sum/difference map identifies
the cap with a parity rectangle; the existing residue-count and
filtered-product suppliers count that rectangle.
The axial theorem consumes this generic balance and supplies the counting
step in the actual maximum-pair growth theorem. No literature novelty or publication priority is claimed.
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

private def upperCap (h : ℤ × ℤ) (r : ℕ) : Finset (ℤ × ℤ) :=
  leeDiamond r ∩ (leeDiamond r).image (fun z => z+h)

private def trimmedDiamond (h : ℤ × ℤ) (r : ℕ) : Finset (ℤ × ℤ) :=
  leeDiamond r \ upperCap h r

private theorem mem_upperCap {h : ℤ × ℤ} {r : ℕ} {z : ℤ × ℤ} :
    z ∈ upperCap h r ↔ z ∈ leeDiamond r ∧ z-h ∈ leeDiamond r := by
  simp only [upperCap, Finset.mem_inter, Finset.mem_image]
  constructor
  · rintro ⟨hz,w,hw,rfl⟩
    exact ⟨hz, by simpa using hw⟩
  · rintro ⟨hz,hzm⟩
    exact ⟨hz,z-h,hzm,sub_add_cancel _ _⟩

private theorem leeNorm_add (x y : ℤ × ℤ) :
    leeNorm (x+y) ≤ leeNorm x+leeNorm y := by
  dsimp [leeNorm]
  change |x.1+y.1|+|x.2+y.2| ≤ |x.1|+|x.2|+(|y.1|+|y.2|)
  linarith [abs_add_le x.1 y.1, abs_add_le x.2 y.2]

private theorem leeNorm_zsmul (k : ℤ) (z : ℤ × ℤ) :
    leeNorm (k • z) = |k| * leeNorm z := by
  change |k*z.1|+|k*z.2| = |k| * (|z.1|+|z.2|)
  rw [abs_mul, abs_mul, mul_add]

/-- Integer interpolation on a fiber: for positive k, y-h lies between
x and y when y-x = k • h. No real-vector-space structure is used. -/
private theorem leeDiamond_sub_mem_of_pos_multiple {x y h : ℤ × ℤ}
    {r : ℕ} {k : ℤ} (hx : x ∈ leeDiamond r) (hy : y ∈ leeDiamond r)
    (hk : 0 < k) (hxy : y-x = k • h) : y-h ∈ leeDiamond r := by
  have hk0 : 0 ≤ k := le_of_lt hk
  have hkm0 : 0 ≤ k-1 := by omega
  have hx' : x = y-k • h := by rw [← hxy]; abel
  have hline : k • (y-h) = (k-1) • y+x := by
    rw [hx', smul_sub, sub_smul, one_smul]
    abel
  have hweighted : k*leeNorm (y-h) ≤ (k-1)*leeNorm y+leeNorm x := by
    calc
      k*leeNorm (y-h) = leeNorm (k • (y-h)) := by
        rw [leeNorm_zsmul, abs_of_nonneg hk0]
      _ = leeNorm ((k-1) • y+x) := by rw [hline]
      _ ≤ leeNorm ((k-1) • y)+leeNorm x := leeNorm_add _ _
      _ = (k-1)*leeNorm y+leeNorm x := by
        rw [leeNorm_zsmul, abs_of_nonneg hkm0]
  have hxbound : leeNorm x ≤ (r : ℤ) := mem_leeDiamond.mp hx
  have hybound : leeNorm y ≤ (r : ℤ) := mem_leeDiamond.mp hy
  have hmul : k*leeNorm (y-h) ≤ k*(r : ℤ) := by
    calc
      k*leeNorm (y-h) ≤ (k-1)*leeNorm y+leeNorm x := hweighted
      _ ≤ (k-1)*(r : ℤ)+(r : ℤ) :=
        add_le_add (mul_le_mul_of_nonneg_left hybound hkm0) hxbound
      _ = k*(r : ℤ) := by ring
  exact mem_leeDiamond.mpr (le_of_mul_le_mul_left hmul hk)

/-- The single shared fiber proof: the trimmed diamond retains precisely
one bottom point of each finite fiber parallel to the nonzero vector h. -/
private theorem trim_bijOn {G : Type u} [AddCommGroup G]
    (f : (ℤ × ℤ) →+ G) {h : ℤ × ℤ} {r : ℕ} (hne : h ≠ 0)
    (hh : f h = 0)
    (hshort : ∀ z : ℤ × ℤ, |z.1|+|z.2| ≤ 2*(r : ℤ) → f z = 0 →
      ∃ k : ℤ, z = k • h) :
    Set.BijOn f (↑(trimmedDiamond h r) : Set (ℤ × ℤ))
      (↑((leeDiamond r).image f) : Set G) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact Finset.mem_image.mpr ⟨z, (Finset.mem_sdiff.mp hz).1, rfl⟩
  · intro x hx y hy he
    obtain ⟨hxD,hxC⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hyD,hyC⟩ := Finset.mem_sdiff.mp hy
    have hnorm : |(y-x).1|+|(y-x).2| ≤ 2*(r : ℤ) := by
      have ht := norm_sub_le y x
      have h1 := mem_leeDiamond.mp hxD
      have h2 := mem_leeDiamond.mp hyD
      dsimp [leeNorm] at ht
      change |y.1-x.1|+|y.2-x.2| ≤ 2*(r : ℤ)
      linarith
    have hzero : f (y-x) = 0 := by rw [map_sub, he, sub_self]
    obtain ⟨k,hk⟩ := hshort (y-x) hnorm hzero
    rcases lt_trichotomy k 0 with hkneg | hkzero | hkpos
    · have hxy : x-y = (-k) • h := by
        rw [neg_smul, ← hk]
        abel
      have hxm := leeDiamond_sub_mem_of_pos_multiple hyD hxD
        (by omega : 0 < -k) hxy
      exact False.elim (hxC (mem_upperCap.mpr ⟨hxD,hxm⟩))
    · have h0 : y-x = 0 := by simpa only [hkzero, zero_smul] using hk
      exact (sub_eq_zero.mp h0).symm
    · have hym := leeDiamond_sub_mem_of_pos_multiple hxD hyD hkpos hk
      exact False.elim (hyC (mem_upperCap.mpr ⟨hyD,hym⟩))
  · intro g hg
    obtain ⟨z,hz,hzg⟩ := Finset.mem_image.mp hg
    let fiber := (leeDiamond r).filter (fun w => f w = g)
    have hnonempty : fiber.Nonempty := ⟨z, Finset.mem_filter.mpr ⟨hz,hzg⟩⟩
    obtain ⟨w,hw,hmin⟩ := Finset.exists_min_image fiber
      (fun w => w.1*h.1+w.2*h.2) hnonempty
    obtain ⟨hwD,hwf⟩ := Finset.mem_filter.mp hw
    refine ⟨w, Finset.mem_sdiff.mpr ⟨hwD,?_⟩, hwf⟩
    intro hwC
    have hminusD := (mem_upperCap.mp hwC).2
    have hminusf : f (w-h) = g := by rw [map_sub, hh, sub_zero]; exact hwf
    have hminus : w-h ∈ fiber := Finset.mem_filter.mpr ⟨hminusD,hminusf⟩
    have hle := hmin (w-h) hminus
    change w.1*h.1+w.2*h.2 ≤ (w.1-h.1)*h.1+(w.2-h.2)*h.2 at hle
    have hpos : 0 < h.1^2+h.2^2 := by
      by_cases hx : h.1 = 0
      · have hy : h.2 ≠ 0 := by
          intro hy
          exact hne (Prod.ext hx hy)
        have hp := sq_pos_of_ne_zero hy
        nlinarith only [hx, hp]
      · have hp := sq_pos_of_ne_zero hx
        nlinarith only [hp, sq_nonneg h.2]
    nlinarith only [hle, hpos]

-- The widths are integer positive parts, not natural absolute-value subtraction.
private def capWidth (r : ℕ) (t : ℤ) : ℕ :=
  (2*(r : ℤ)+1-|t|).toNat

private def capStart (r : ℕ) (t : ℤ) : ℤ :=
  max (-(r : ℤ)) (t-r)

private def capInterval (r : ℕ) (t : ℤ) : Finset ℤ :=
  Finset.Ico (capStart r t) (min (r : ℤ) (t+r)+1)

private theorem mem_capInterval {r : ℕ} {t x : ℤ} :
    x ∈ capInterval r t ↔ |x| ≤ (r : ℤ) ∧ |x-t| ≤ (r : ℤ) := by
  simp only [capInterval, capStart, Finset.mem_Ico, abs_le]
  omega

private theorem capInterval_coordinates {r : ℕ} {t x : ℤ} :
    x ∈ capInterval r t ↔
      0 ≤ x-capStart r t ∧ x-capStart r t < (capWidth r t : ℤ) := by
  simp only [capInterval, capStart, capWidth, Finset.mem_Ico]
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    omega
  · rw [abs_of_nonpos (by omega : t ≤ 0)]
    omega

private theorem capInterval_card (r : ℕ) (t : ℤ) :
    (capInterval r t).card = capWidth r t := by
  rw [capInterval, Int.card_Ico]
  dsimp [capStart, capWidth]
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    omega
  · rw [abs_of_nonpos (by omega : t ≤ 0)]
    omega

/-- A private translation adapter to the existing residue-count supplier.
For odd nonempty widths the initial point has parity r, for either sign of t. -/
private theorem capInterval_majority_card (r : ℕ) (t : ℤ) :
    ((capInterval r t).filter (fun x => x % 2 = (r : ℤ) % 2)).card =
      (capWidth r t+1)/2 := by
  classical
  let e : ℕ := (((r : ℤ)-capStart r t)%2).toNat
  have he : e < 2 := by dsimp [e]; omega
  have hodd : capWidth r t % 2 = 1 → e = 0 := by
    intro hw
    dsimp [capWidth, e, capStart] at *
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht] at hw
      omega
    · rw [abs_of_nonpos (by omega : t ≤ 0)] at hw
      omega
  have hres (i : ℕ) : i ≡ e [MOD 2] ↔
      (capStart r t+(i : ℤ))%2 = (r : ℤ)%2 := by
    dsimp [Nat.ModEq, e]
    omega
  have hbij : Set.BijOn (fun i : ℕ => capStart r t+(i : ℤ))
      (↑((Finset.range (capWidth r t)).filter (fun i => i ≡ e [MOD 2])) : Set ℕ)
      (↑((capInterval r t).filter (fun x => x%2 = (r : ℤ)%2)) : Set ℤ) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨hi,hm⟩ := Finset.mem_filter.mp hi
      have hi' := Finset.mem_range.mp hi
      refine Finset.mem_filter.mpr ⟨capInterval_coordinates.mpr ?_, (hres i).mp hm⟩
      dsimp only
      constructor <;> omega
    · intro i _ j _ hij
      change capStart r t+(i : ℤ) = capStart r t+(j : ℤ) at hij
      omega
    · intro x hx
      obtain ⟨hx,hp⟩ := Finset.mem_filter.mp hx
      have hc := capInterval_coordinates.mp hx
      have hi : (x-capStart r t).toNat < capWidth r t := by omega
      have hxi : capStart r t+((x-capStart r t).toNat : ℤ) = x := by omega
      refine ⟨(x-capStart r t).toNat, ?_, hxi⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,
        (hres _).mpr (by rwa [hxi])⟩
  have hcard := Set.BijOn.finsetCard_eq (fun i : ℕ => capStart r t+(i : ℤ)) hbij
  have hcount := Nat.count_modEq_card (capWidth r t) (r := 2) (by decide) e
  rw [Nat.count_eq_card_filter_range] at hcount
  rw [← hcard, hcount]
  split_ifs with hp
  · have hw : capWidth r t % 2 = 1 := by omega
    have he0 := hodd hw
    omega
  · have hw : capWidth r t % 2 = 0 := by
      by_contra hn
      have hw : capWidth r t % 2 = 1 := by omega
      have he0 := hodd hw
      omega
    omega

private theorem capInterval_minority_card (r : ℕ) (t : ℤ) :
    ((capInterval r t).filter (fun x => ¬ x % 2 = (r : ℤ) % 2)).card =
      capWidth r t/2 := by
  have h := Finset.card_filter_add_card_filter_not (s := capInterval r t)
    (fun x => x%2 = (r : ℤ)%2)
  rw [capInterval_majority_card, capInterval_card] at h
  omega

/-- S is kept on integer pairs; its inverse on equal-parity pairs uses /2. -/
private def capSumDiff (z : ℤ × ℤ) : ℤ × ℤ := (z.1+z.2,z.1-z.2)

private def capRectangle (h : ℤ × ℤ) (r : ℕ) : Finset (ℤ × ℤ) :=
  ((capInterval r (h.1+h.2)) ×ˢ (capInterval r (h.1-h.2))).filter
    (fun q => (q.1%2 = (r : ℤ)%2) = (q.2%2 = (r : ℤ)%2))

private theorem capSumDiff_bijOn (h : ℤ × ℤ) (r : ℕ) :
    Set.BijOn capSumDiff (↑(upperCap h r) : Set (ℤ × ℤ))
      (↑(capRectangle h r) : Set (ℤ × ℤ)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨hz,hm⟩ := mem_upperCap.mp hz
    have hz' := (LeeSquareCompression.lee_iff_square _ _ _).mp (mem_leeDiamond.mp hz)
    have hm' := (LeeSquareCompression.lee_iff_square _ _ _).mp (mem_leeDiamond.mp hm)
    change |z.1-h.1+(z.2-h.2)| ≤ (r : ℤ) ∧
      |z.1-h.1-(z.2-h.2)| ≤ (r : ℤ) at hm'
    have hsum : (z.1+z.2)-(h.1+h.2) = z.1-h.1+(z.2-h.2) := by ring
    have hdiff : (z.1-z.2)-(h.1-h.2) = z.1-h.1-(z.2-h.2) := by ring
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact mem_capInterval.mpr ⟨hz'.1, by simpa only [capSumDiff, hsum] using hm'.1⟩
    · exact mem_capInterval.mpr ⟨hz'.2, by simpa only [capSumDiff, hdiff] using hm'.2⟩
    · dsimp [capSumDiff]
      apply propext
      omega
  · intro x _ y _ he
    have h0 := congrArg Prod.fst he
    have h1 := congrArg Prod.snd he
    dsimp [capSumDiff] at h0 h1
    apply Prod.ext <;> omega
  · intro q hq
    obtain ⟨hq,hp⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq0,hq1⟩ := Finset.mem_product.mp hq
    have h0 := mem_capInterval.mp hq0
    have h1 := mem_capInterval.mp hq1
    have hp' : q.1%2 = q.2%2 := by
      have hpiff := Iff.of_eq hp
      omega
    let z : ℤ × ℤ := ((q.1+q.2)/2,(q.1-q.2)/2)
    have hz0 : z.1+z.2 = q.1 := by dsimp [z]; omega
    have hz1 : z.1-z.2 = q.2 := by dsimp [z]; omega
    refine ⟨z, mem_upperCap.mpr ⟨?_, ?_⟩, Prod.ext hz0 hz1⟩
    · apply mem_leeDiamond.mpr
      apply (LeeSquareCompression.lee_iff_square _ _ _).mpr
      simpa only [hz0,hz1] using And.intro h0.1 h1.1
    · apply mem_leeDiamond.mpr
      apply (LeeSquareCompression.lee_iff_square _ _ _).mpr
      change |z.1-h.1+(z.2-h.2)| ≤ (r : ℤ) ∧
        |z.1-h.1-(z.2-h.2)| ≤ (r : ℤ)
      have he0 : z.1-h.1+(z.2-h.2) = q.1-(h.1+h.2) := by
        calc
          _ = (z.1+z.2)-(h.1+h.2) := by ring
          _ = _ := by rw [hz0]
      have he1 : z.1-h.1-(z.2-h.2) = q.2-(h.1-h.2) := by
        calc
          _ = (z.1-z.2)-(h.1-h.2) := by ring
          _ = _ := by rw [hz1]
      simpa only [he0,he1] using And.intro h0.2 h1.2

private theorem parity_product_halves (A B : ℕ) :
    ((A+1)/2)*((B+1)/2)+(A/2)*(B/2) = (A*B+1)/2 := by
  have ha : A = 2*(A/2)+A%2 := by omega
  have hb : B = 2*(B/2)+B%2 := by omega
  have ha' : (A+1)/2 = A/2+A%2 := by omega
  have hb' : (B+1)/2 = B/2+B%2 := by omega
  rw [ha', hb']
  have hab : A*B = (2*(A/2)+A%2)*(2*(B/2)+B%2) := by
    conv_lhs => rw [ha,hb]
  have ha2 : A%2 = 0 ∨ A%2 = 1 := by omega
  have hb2 : B%2 = 0 ∨ B%2 = 1 := by omega
  rcases ha2 with ha2 | ha2 <;> rcases hb2 with hb2 | hb2
  all_goals
    rw [ha2,hb2] at hab ⊢
    have hlo : 2*((A/2+ A%2)*(B/2+B%2)+(A/2)*(B/2)) ≤ A*B+1 := by
      rw [ha2,hb2]
      nlinarith [hab]
    have hhi : A*B+1 < 2*(((A/2+A%2)*(B/2+B%2)+(A/2)*(B/2))+1) := by
      rw [ha2,hb2]
      nlinarith [hab]
    simp only [ha2,hb2] at hlo hhi
    omega

private theorem upperCap_card (h : ℤ × ℤ) (r : ℕ) :
    (upperCap h r).card =
      (capWidth r (h.1+h.2)*capWidth r (h.1-h.2)+1)/2 := by
  have hcard := Set.BijOn.finsetCard_eq capSumDiff (capSumDiff_bijOn h r)
  rw [hcard, capRectangle, Finset.filter_product_card _ _
    (fun x : ℤ => x%2 = (r : ℤ)%2) (fun y : ℤ => y%2 = (r : ℤ)%2),
    capInterval_majority_card, capInterval_majority_card,
    capInterval_minority_card, capInterval_minority_card]
  exact parity_product_halves _ _

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

/-- A nonzero displacement spanning every short kernel vector determines the Lee image.
The balance form avoids any ambiguity from natural truncated subtraction.
No finiteness, surjectivity, sign condition, or extra radius bound is needed. -/
theorem lee_ball_image_card_of_displacement {G : Type u} [AddCommGroup G]
    (f : (ℤ × ℤ) →+ G) {h : ℤ × ℤ} {r : ℕ} (hne : h ≠ 0)
    (hh : f h = 0)
    (hshort : ∀ z : ℤ × ℤ, |z.1|+|z.2| ≤ 2*(r : ℤ) → f z = 0 →
      ∃ k : ℤ, z = k • h) :
    let A := (2*(r : ℤ)+1-|h.1+h.2|).toNat
    let B := (2*(r : ℤ)+1-|h.1-h.2|).toNat
    ((leeDiamond r).image f).card + (A*B+1)/2 = 2*r^2+2*r+1 := by
  classical
  have hbij := trim_bijOn f hne hh hshort
  have hcard := Set.BijOn.finsetCard_eq f hbij
  have hsub : upperCap h r ⊆ leeDiamond r := by
    intro z hz
    exact (mem_upperCap.mp hz).1
  have hbalance := Finset.card_sdiff_add_card_eq_card hsub
  change (trimmedDiamond h r).card + (upperCap h r).card =
    (leeDiamond r).card at hbalance
  rw [hcard, upperCap_card, leeDiamond_card] at hbalance
  exact hbalance

/-- The axial API specializes the displacement balance. Its radius premise
is supplied by the actual maximum-pair consumer. -/
theorem lee_ball_image_card_of_short_kernel {G : Type u} [AddCommGroup G]
    (f : (ℤ × ℤ) →+ G) {B r : ℕ} (hB : 0 < B) (hBr : r < 2*B)
    (hh : f (0,2*(B : ℤ)) = 0)
    (hshort : ∀ z : ℤ × ℤ, |z.1|+|z.2| ≤ 2*(r : ℤ) → f z = 0 →
      z = 0 ∨ z = (0,2*(B : ℤ)) ∨ z = (0,-2*(B : ℤ))) :
    ((leeDiamond r).image f).card =
      if r < B then 2*r^2+2*r+1 else 2*B*(2*r-B+1) := by
  classical
  have hne : (0,2*(B : ℤ)) ≠ (0 : ℤ × ℤ) := by
    intro he
    have hc := congrArg Prod.snd he
    change 2*(B : ℤ) = 0 at hc
    omega
  have hshort' : ∀ z : ℤ × ℤ, |z.1|+|z.2| ≤ 2*(r : ℤ) → f z = 0 →
      ∃ k : ℤ, z = k • (0,2*(B : ℤ)) := by
    intro z hz hzero
    rcases hshort z hz hzero with h0 | hp | hn
    · exact ⟨0, by simpa only [zero_smul] using h0⟩
    · exact ⟨1, by simpa only [one_smul] using hp⟩
    · exact ⟨-1, by
        simpa only [neg_one_smul, Prod.neg_mk, neg_zero, neg_mul] using hn⟩
  have hbalance := lee_ball_image_card_of_displacement f hne hh hshort'
  have hB0 : (0 : ℤ) ≤ 2*(B : ℤ) := by positivity
  simp only [zero_add, zero_sub, abs_neg, abs_of_nonneg hB0] at hbalance
  let W : ℕ := (2*(r : ℤ)+1-2*(B : ℤ)).toNat
  change ((leeDiamond r).image f).card + (W*W+1)/2 =
    2*r^2+2*r+1 at hbalance
  by_cases hr : r < B
  · have hw : W = 0 := by dsimp [W]; omega
    rw [hw] at hbalance
    simpa [if_pos hr] using hbalance
  · rw [if_neg hr]
    have hw : W = 2*(r-B)+1 := by dsimp [W]; omega
    have hcap : (W*W+1)/2 = 2*(r-B)^2+2*(r-B)+1 := by
      rw [hw]
      have he : (2*(r-B)+1)*(2*(r-B)+1)+1 =
          2*(2*(r-B)^2+2*(r-B)+1) := by ring
      rw [he]
      omega
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

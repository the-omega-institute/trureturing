/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualFirstThree/Masked
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-physical-mask-partitions)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Actual paired source sums and physical inventories for complementary chain masks. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Natural

/-! Every split partitions occurrences rather than numerical source values. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
open SourceWidth PeriodicShortening RunFirstEarTransport
open private rank amplitude oldRow newRow mask_data
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Physical
open private natural_inventory
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Natural
open private chainMask chainMask_partition
  from D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventual

private structure Pair (f g : ℕ → ℤ) (off len : ℕ) (F G : ℤ) (m : ℕ) where
  left : List ℕ
  right : List ℕ
  perm : (left ++ right).Perm (List.range' off len)
  fl : (left.map f).sum = (m : ℤ) * F
  fr : (right.map f).sum = ((2 : ℤ) ^ len - 1 - m) * F
  gl : (left.map g).sum = (m : ℤ) * G
  gr : (right.map g).sum = ((2 : ℤ) ^ len - 1 - m) * G
  plf : ∀ i ∈ left, 0 ≤ f i
  prf : ∀ i ∈ right, 0 ≤ f i
  plg : ∀ i ∈ left, 0 ≤ g i
  prg : ∀ i ∈ right, 0 ≤ g i

private noncomputable def split_pair (f g : ℕ → ℤ) (off len m : ℕ)
    (F G : ℤ) (hm : m < 2 ^ len) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hf : ∀ i < len, f (off + i) = (2 : ℤ) ^ i * F)
    (hg : ∀ i < len, g (off + i) = (2 : ℤ) ^ i * G) :
    Pair f g off len F G m := by
  let n := 2 ^ len - 1 - m
  have hp : 0 < 2 ^ len := by positivity
  have hn : n < 2 ^ len := by dsimp [n]; omega
  have hs : m + n = 2 ^ len - 1 := by dsimp [n]; omega
  have hc : (n : ℤ) = (2 : ℤ) ^ len - 1 - m := by
    have he : m + n + 1 = 2 ^ len := by omega
    have hz : (m : ℤ) + n + 1 = (2 : ℤ) ^ len := by exact_mod_cast he
    omega
  have lf := mask_data len off m hm f F hF hf
  have rf := mask_data len off n hn f F hF hf
  have lg := mask_data len off m hm g G hG hg
  have rg := mask_data len off n hn g G hG hg
  exact ⟨chainMask len off m,chainMask len off n,
    chainMask_partition len off m n hs,lf.1,by rw [rf.1,hc],
    lg.1,by rw [rg.1,hc],lf.2,rf.2,lg.2,rg.2⟩

private theorem pair_inventory (s d : ℕ) (hs : 2 ≤ s) (hd : 2 ≤ d)
    (f g : ℕ → ℤ) (A An V Vn W Wn X Xn : ℤ) (u v w x : ℕ)
    (U : Pair f g 0 (d-1) A An u)
    (P : Pair f g d (s-1) V Vn v)
    (Q : Pair f g (d+s) (s-1) W Wn w)
    (T : Pair f g (d+s+s) (s-1) X Xn x) :
    ((U.left ++ U.right) ++ (d-1) ::
      (P.left ++ P.right) ++ (d+s-1) ::
      (Q.left ++ Q.right) ++ (d+s+s-1) ::
      (T.left ++ T.right) ++ [d+s+s+s-1]).Perm (List.range (rank s d)) := by
  have hp := U.perm.append (List.Perm.cons (d-1) (P.perm.append
    (List.Perm.cons (d+s-1) (Q.perm.append (List.Perm.cons (d+s+s-1)
      (T.perm.append (List.Perm.refl [d+s+s+s-1])))))))
  have hn := natural_inventory s d hs hd
  have hpn : ((U.left ++ U.right) ++ (d-1) ::
      (P.left ++ P.right) ++ (d+s-1) ::
      (Q.left ++ Q.right) ++ (d+s+s-1) ::
      (T.left ++ T.right) ++ [d+s+s+s-1]).Perm
      (List.range' 0 (d-1) ++ (d-1) :: List.range' d (s-1) ++
        (d+s-1) :: List.range' (d+s) (s-1) ++
        (d+s+s-1) :: List.range' (d+s+s) (s-1) ++ [d+s+s+s-1]) := by
    simpa only [List.append_assoc, List.cons_append] using hp
  exact hpn.trans hn

end D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree

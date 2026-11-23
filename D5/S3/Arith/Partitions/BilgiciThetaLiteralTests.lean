/- GID: D5/S3/Arith/Partitions/BilgiciThetaLiteralTests
   generality: I
   mirror-B: D5/B/S3/Arith/Partitions/BilgiciThetaLiteralTests
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full weight-eleven component satisfies the trace and dual-number tests. -/

import D5.S3.Arith.Partitions.BilgiciThetaGrading
import D5.S3.Arith.Partitions.BilgiciThetaDetectors
import Mathlib.FieldTheory.Finite.Basic

/-! The full weight-eleven component satisfies the trace and dual-number tests. -/

open D5.S3.Arith.Partitions.BilgiciThetaQuartic hiding digit
open MvPolynomial
open scoped BigOperators

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural
open D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening (x x_int x_odd x_zero x_abs x_digit abs_square absIndex digit T_x raw)

private def intPositive : Finset ℤ := Finset.Icc 1 9

def positive : Finset K := intPositive.image (fun a : ℤ => (a : K))

private theorem val_cast_of_positive {a : ℤ} (ha : a ∈ intPositive) :
    (((a : K).val : ℕ) : ℤ) = a := by
  rw [ZMod.val_intCast]
  have h := Finset.mem_Icc.mp ha
  omega

private theorem positive_cast_inj : Set.InjOn (fun a : ℤ => (a : K)) ↑intPositive := by
  intro a ha b hb hab
  change (a : K) = (b : K) at hab
  rw [← val_cast_of_positive ha, ← val_cast_of_positive hb, hab]

private theorem sum_even_field {M : Type*} [AddCommMonoid M] (f : K → M)
    (h0 : f 0 = 0) (he : ∀ a, f (-a) = f a) :
    ∑ a : K, f a = ∑ a ∈ positive, f a + ∑ a ∈ positive, f a := by
  have cover : (Finset.univ : Finset K) =
      insert 0 (positive ∪ positive.image Neg.neg) := by decide
  have hzero : (0 : K) ∉ positive ∪ positive.image Neg.neg := by decide
  have hdisj : Disjoint positive (positive.image Neg.neg) := by decide
  rw [cover, Finset.sum_insert hzero, h0, zero_add, Finset.sum_union hdisj,
    Finset.sum_image (fun _ _ _ _ h => neg_injective h)]
  simp only [he]

private noncomputable def signedC (a : K) : R := C a * x a

private noncomputable def signedB (a b : K) : R :=
  C ((3 / 8 : K) * a * b * (b^2 - a^2)) * (x a * x b) * (x (a+b) * x (a-b))

private theorem signedC_even (a : K) : signedC (-a) = signedC a := by
  simp [signedC, x_odd]

private theorem signedB_even_left (a b : K) : signedB (-a) b = signedB a b := by
  rw [signedB, signedB, show -a+b = -(a-b) by ring, show -a-b = -(a+b) by ring]
  simp only [x_odd, neg_sq, mul_neg, neg_mul, neg_neg, map_neg]
  ring

private theorem signedB_even_right (a b : K) : signedB a (-b) = signedB a b := by
  rw [signedB, signedB, show a + -b = a-b by ring, show a - -b = a+b by ring]
  simp only [x_odd, neg_sq, mul_neg, neg_mul, neg_neg, map_neg]
  ring

private theorem signedB_swap (a b : K) : signedB b a = signedB a b := by
  rw [signedB, signedB, show a^2 - b^2 = -(b^2 - a^2) by ring,
    show b-a = -(a-b) by ring, x_odd, add_comm b a]
  simp only [mul_neg, map_neg, neg_mul]
  ring

private theorem paperC_field_sum : paperC = ∑ a : K, signedC a := by
  rw [sum_even_field signedC (by simp [signedC]) signedC_even, ← Finset.sum_add_distrib,
    positive, Finset.sum_image positive_cast_inj, paperC]
  apply Finset.sum_congr rfl
  intro a ha
  rw [signedC, x_int, ← mul_assoc, ← map_mul, ← add_mul, ← map_add]
  congr 2
  unfold cCoefficient;
  ring

private def positiveTriangle : Finset (K × K) :=
  (positive ×ˢ positive).filter (fun p => p.1.val < p.2.val)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem signedB_positive_square (s : Finset K) :
    ∑ a ∈ s, ∑ b ∈ s, signedB a b =
      (∑ p ∈ (s ×ˢ s).filter (fun p => p.1.val < p.2.val), signedB p.1 p.2) +
        ∑ p ∈ (s ×ˢ s).filter (fun p => p.1.val < p.2.val), signedB p.1 p.2 := by
  let tri := (s ×ˢ s).filter (fun p => p.1.val < p.2.val)
  change (∑ a ∈ s, ∑ b ∈ s, signedB a b) = (∑ p ∈ tri, _) + (∑ p ∈ tri, _)
  let swap : K × K ↪ K × K := (Equiv.prodComm K K).toEmbedding
  let diag := (s ×ˢ s).filter (fun p => p.1 = p.2)
  have hswap (p : K × K) : p ∈ tri.map swap ↔
      p ∈ s ×ˢ s ∧ p.2.val < p.1.val := by
    rcases p with ⟨a,b⟩
    simp only [Finset.mem_map, tri, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨u,v⟩, ⟨⟨hu,hv⟩, ht⟩, h⟩
      change (v,u) = (a,b) at h
      cases h
      exact ⟨⟨hv,hu⟩,ht⟩
    · rintro ⟨⟨ha,hb⟩,ht⟩
      exact ⟨(b,a), ⟨⟨hb,ha⟩,ht⟩, rfl⟩
  have cover : s ×ˢ s =
      (tri ∪ tri.map swap) ∪ diag := by
    apply Finset.ext
    intro p
    rw [Finset.mem_union, Finset.mem_union, hswap]
    simp only [tri, diag, Finset.mem_filter]
    constructor
    · intro hp
      rcases lt_trichotomy p.1.val p.2.val with hl | he | hg
      · exact Or.inl (Or.inl ⟨hp,hl⟩)
      · exact Or.inr ⟨hp, ZMod.val_injective 19 he⟩
      · exact Or.inl (Or.inr ⟨hp,hg⟩)
    · rintro ((⟨hp,_⟩ | ⟨hp,_⟩) | ⟨hp,_⟩) <;> exact hp
  have hdiag : Disjoint (tri ∪ tri.map swap) diag := by
    rw [Finset.disjoint_left]
    intro p h₁ h₂
    have he : p.1 = p.2 := (Finset.mem_filter.mp h₂).2
    rcases Finset.mem_union.mp h₁ with ht | ht
    · exact (lt_irrefl _) (he ▸ (Finset.mem_filter.mp ht).2)
    · exact (lt_irrefl _) (he ▸ (hswap p).mp ht |>.2)
  have htri : Disjoint tri (tri.map swap) := by
    rw [Finset.disjoint_left]
    intro p h₁ h₂
    exact (not_lt_of_ge (Finset.mem_filter.mp h₁).2.le) (hswap p |>.mp h₂ |>.2)
  let f := fun p : K × K => signedB p.1 p.2
  have hz : ∑ p ∈ diag, f p = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have he := (Finset.mem_filter.mp hp).2
    simp [f, signedB, he]
  have hflip : ∑ p ∈ tri.map swap, f p = ∑ p ∈ tri, f p := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro p _
    exact signedB_swap p.1 p.2
  calc
    (∑ a ∈ s, ∑ b ∈ s, signedB a b) = ∑ p ∈ s ×ˢ s, f p :=
      (Finset.sum_product' s s (fun a b => signedB a b)).symm
    _ = ∑ p ∈ (tri ∪ tri.map swap) ∪ diag, f p := congrArg (fun t => ∑ p ∈ t, f p) cover
    _ = (∑ p ∈ tri, f p) + (∑ p ∈ tri, f p) := by
      rw [Finset.sum_union hdiag, Finset.sum_union htri, hflip, hz, add_zero]

private theorem signedB_field_sum_triangle :
    ∑ a : K, ∑ b : K, signedB a b =
      ∑ p ∈ positiveTriangle, (8 : K) • signedB p.1 p.2 := by
  rw [sum_even_field (fun a => ∑ b : K, signedB a b)
    (by simp [signedB]) (fun a => by simp only [signedB_even_left])]
  simp_rw [sum_even_field (signedB _) (by simp [signedB]) (signedB_even_right _)]
  rw [Finset.sum_add_distrib, signedB_positive_square positive]
  rw [← Finset.smul_sum]
  let z : R := ∑ p ∈ positiveTriangle, signedB p.1 p.2
  change z+z+(z+z)+(z+z+(z+z)) = (8 : K) • z
  rw [smul_eq_C_mul, show (C (8 : K) : R) = 8 from map_ofNat C 8]
  ring

private theorem positiveTriangle_image : positiveTriangle =
    (((intPositive ×ˢ intPositive).filter (fun p => p.1 < p.2)).image
      (fun p : ℤ × ℤ => ((p.1 : K), (p.2 : K)))) := by decide

private theorem positiveTriangle_inj : Set.InjOn
    (fun p : ℤ × ℤ => ((p.1 : K), (p.2 : K)))
    ↑((intPositive ×ˢ intPositive).filter (fun p => p.1 < p.2)) := by
  intro a ha b hb h
  obtain ⟨ha1, ha2⟩ := Finset.mem_product.mp (Finset.mem_filter.mp ha).1
  obtain ⟨hb1, hb2⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hb).1
  exact Prod.ext (positive_cast_inj ha1 hb1 (congrArg Prod.fst h))
    (positive_cast_inj ha2 hb2 (congrArg Prod.snd h))

private theorem signedB_int (a b : ℤ) :
    (8 : K) • signedB (a : K) (b : K) =
      C (bCoefficient a b) * ((Z a * Z b) * (Z (a+b) * Z (b-a))) := by
  rw [signedB, smul_eq_C_mul, ← Int.cast_add, ← Int.cast_sub, x_int, x_int, x_int, x_int]
  rw [show a-b = -(b-a) by ring, Z_neg]
  have hs : sign (a+b + -(b-a)) = 1 := by
    unfold sign;
    rw [ite_eq_left (by omega)]
  rw [mul_mul_mul_comm (C (sign a)) _ (C (sign b)),
    mul_mul_mul_comm (C (sign (a+b))) _ (C (sign (-(b-a)))),
    ← map_mul, ← map_mul, ← sign_add, ← sign_add, hs, map_one, one_mul]
  have hcoeff : -(8 : K) * (((3 / 8 : K) * (a : K) * (b : K) *
      ((b : K)^2 - (a : K)^2)) * sign (a+b)) = bCoefficient a b := by
    have heq : -(8 : K) * (((3 / 8 : K) * (a : K) * (b : K) *
        ((b : K)^2 - (a : K)^2)) * sign (a+b)) =
        -((8 : K)*(3/8)) * sign (a+b) * (a : K) * (b : K) *
          ((b : K)^2 - (a : K)^2) := by ring
    rw [heq, show (8 : K) * (3/8) = 3 by rw [mul_comm, div_mul_cancel₀ _ (by decide : (8 : K) ≠ 0)]]
    rfl
  have h : C (-(8 : K)) * C (((3 / 8 : K) * (a : K) * (b : K) *
      ((b : K)^2 - (a : K)^2))) * C (sign (a+b)) =
      (C (bCoefficient a b) : R) := by
    rw [← map_mul, ← map_mul, mul_assoc, hcoeff]
  calc
    _ = (C (-(8 : K)) * C (((3 / 8 : K) * (a : K) * (b : K) *
        ((b : K)^2 - (a : K)^2))) * C (sign (a+b))) *
         ((Z a * Z b) * (Z (a+b) * Z (b-a))) := by rw [map_neg]; ring
    _ = _ := by rw [h]

private theorem paperB_field_sum : paperB = ∑ a : K, ∑ b : K, signedB a b := by
  rw [signedB_field_sum_triangle, positiveTriangle_image, Finset.sum_image positiveTriangle_inj,
    paperB]
  apply Finset.sum_congr rfl
  intro p _
  exact (signedB_int p.1 p.2).symm

private def centerOf (a b c d e : K) : K := 3*(a^2+b^2)+c^2+d^2+e^2

private noncomputable def signedProduct (a b c d e : K) : R :=
  ((signedB a b * signedC c) * signedC d) * signedC e

private theorem signedProduct_word (a b c d e : K) :
    signedProduct a b c d e =
      ((3/8 : K)*a*b*(b^2-a^2)*c*d*e) • raw [a,b,a+b,a-b,c,d,e] := by
  simp only [raw, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, signedProduct,
    signedB, signedC, smul_eq_C_mul, map_mul]
  ring

private theorem weighted_signedProduct (a b c d e : K) :
    weightedHomogeneousComponent w (11 : K) (signedProduct a b c d e) =
      if centerOf a b c d e = 0 then signedProduct a b c d e else 0 := by
  rw [signedProduct_word]
  let l : List K := [a,b,a+b,a-b,c,d,e]
  by_cases hz : ∃ r ∈ l, r = 0
  · obtain ⟨r, hr, rfl⟩ := hz
    have hprod : raw l = 0 := List.prod_eq_zero (List.mem_map.mpr ⟨0,hr,x_zero⟩)
    change weightedHomogeneousComponent w (11 : K) (_ • raw l) =
      (if centerOf a b c d e = 0 then _ • raw l else 0)
    simp [hprod]
  · have ha (r : K) (hr : r ∈ l) : r ≠ 0 := fun h => hz ⟨r, hr, h⟩
    let m := D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening.absWord l
    have hlen : m.length = 7 := rfl
    have hcenter : centered m = centerOf a b c d e := by
      change (l.map fun r => digit (absIndex r) ^ 2).sum = _
      have hmaps : (l.map fun r => digit (absIndex r) ^ 2) = l.map (· ^ 2) :=
        List.map_congr_left (fun r hr => abs_square r (ha r hr))
      rw [hmaps]
      change a^2+(b^2+((a+b)^2+((a-b)^2+(c^2+(d^2+(e^2+0)))))) = _
      unfold centerOf
      ring
    have hword : raw l = D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening.coeff l •
        ((m.map (fun i => sign (index i))).prod • word m) :=
      (D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening.raw_abs l).trans (congrArg (_ • ·) (D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening.source_word_sign m))
    have hw := centered_zero_iff m 7 11 hlen (by decide)
    rw [← hcenter, hword]
    simp only [map_smul]
    by_cases hm : centered m = 0
    · rw [ite_eq_left hm, (grade_mem.mp (word_grade hlen (hw.mp hm))).2.weightedHomogeneousComponent_same]
    · have hne : (11 : K) ≠ wordWeight m := fun h => hm (hw.mpr h.symm)
      rw [ite_eq_right hm, (grade_mem.mp (word_grade hlen rfl)).2.weightedHomogeneousComponent_ne _ hne,
        smul_zero, smul_zero, smul_zero]

set_option maxHeartbeats 1000000 in
private theorem literalF11_field_sum :
    F11 = ∑ a : K, ∑ b : K, ∑ c : K, ∑ d : K, ∑ e : K,
      if centerOf a b c d e = 0 then signedProduct a b c d e else 0 := by
  have hC (p : R) : p * paperC = ∑ c : K, p * signedC c := by
    rw [paperC_field_sum, Finset.mul_sum]
  have hprod (a b : K) : signedB a b * paperC^3 =
      ∑ c : K, ∑ d : K, ∑ e : K, signedProduct a b c d e := by
    simp only [signedProduct, ← hC, ← Finset.sum_mul]
    ring
  unfold F11
  simp only [paperB_field_sum, Finset.sum_mul]
  simp only [hprod, map_sum, weighted_signedProduct]

end D5.S3.Arith.Partitions.BilgiciThetaStructural

open D5.S3.Arith.Partitions.BilgiciThetaQuartic hiding digit
open MvPolynomial
open scoped BigOperators

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural
open D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening (x x_odd T_x raw)

def g : K := -2

private theorem g_ne_zero : g ≠ 0 := by decide

private theorem T_signed_index (a : K) : T (x a) = x (g*a) := by
  rw [T_x, ← x_odd]
  congr 1
  unfold g
  ring

private theorem T_raw (m : List K) : T (raw m) = raw (m.map (g * ·)) := by
  induction m with
  | nil => exact map_one T
  | cons r m ih =>
    change T (x r * raw m) = x (g*r) * raw (m.map (g * ·))
    rw [map_mul, T_signed_index, ih]

private theorem T_signedProduct (a b c d e : K) :
    T (signedProduct a b c d e) = (4 : K) •
      signedProduct (g*a) (g*b) (g*c) (g*d) (g*e) := by
  rw [signedProduct_word, signedProduct_word, map_smul, T_raw, smul_smul]
  simp only [List.map_cons, List.map_nil]
  rw [show g*a+g*b = g*(a+b) by ring, show g*a-g*b = g*(a-b) by ring]
  have h4 : (4 : K)*g^7 = 1 := by decide
  have hc : (4 : K) * ((3/8 : K) * (g*a) * (g*b) * ((g*b)^2-(g*a)^2) *
        (g*c) * (g*d) * (g*e)) =
      (3/8 : K) * a * b * (b^2-a^2) * c * d * e := by
    calc
      _ = ((4 : K)*g^7) * ((3/8 : K) * a * b * (b^2-a^2) * c * d * e) := by ring
      _ = _ := by rw [h4,one_mul]
  rw [hc]

private theorem center_scale (a b c d e : K) :
    centerOf (g*a) (g*b) (g*c) (g*d) (g*e) = 0 ↔ centerOf a b c d e = 0 := by
  rw [show centerOf (g*a) (g*b) (g*c) (g*d) (g*e) = g^2 * centerOf a b c d e by
    unfold centerOf
    ring]
  simp [g_ne_zero]

private theorem five_sum_mul_reindex {M : Type*} [AddCommMonoid M] (f : K → K → K → K → K → M) :
    (∑ a : K, ∑ b : K, ∑ c : K, ∑ d : K, ∑ e : K, f (g*a) (g*b) (g*c) (g*d) (g*e)) =
      ∑ a : K, ∑ b : K, ∑ c : K, ∑ d : K, ∑ e : K, f a b c d e := by
  let s := Equiv.mulLeft₀ g g_ne_zero
  change (∑ a : K, ∑ b : K, ∑ c : K, ∑ d : K, ∑ e : K, f (s a) (s b) (s c) (s d) (s e)) = _
  refine (Equiv.sum_comp s (fun a => ∑ b : K, ∑ c : K, ∑ d : K, ∑ e : K,
    f a (s b) (s c) (s d) (s e))).trans ?_
  apply Finset.sum_congr rfl
  intro a _
  refine (Equiv.sum_comp s (fun b => ∑ c : K, ∑ d : K, ∑ e : K,
    f a b (s c) (s d) (s e))).trans ?_
  apply Finset.sum_congr rfl
  intro b _
  refine (Equiv.sum_comp s (fun c => ∑ d : K, ∑ e : K, f a b c (s d) (s e))).trans ?_
  apply Finset.sum_congr rfl
  intro c _
  refine (Equiv.sum_comp s (fun d => ∑ e : K, f a b c d (s e))).trans ?_
  apply Finset.sum_congr rfl
  intro d _
  exact Equiv.sum_comp s (f a b c d)

set_option maxHeartbeats 1000000 in
private theorem literalF11_character : T F11 = (4 : K) • F11 := by
  rw [literalF11_field_sum]
  let f := fun a b c d e : K =>
    if centerOf a b c d e = 0 then signedProduct a b c d e else 0
  change T (∑ a : K, ∑ b : K, ∑ c : K, ∑ d : K, ∑ e : K, f a b c d e) = _
  have h (a b c d e : K) : T (f a b c d e) = (4 : K) •
      f (g*a) (g*b) (g*c) (g*d) (g*e) := by
    simp only [f, center_scale]
    split_ifs
    · exact T_signedProduct a b c d e
    · simp
  simp only [map_sum, h, ← Finset.smul_sum, five_sum_mul_reindex f]
  rfl

private theorem signedProduct_homogeneous (a b c d e : K) :
    (signedProduct a b c d e).IsHomogeneous 7 := by
  rw [signedProduct_word, D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening.raw_abs, D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening.source_word_sign]
  have hw := word_grade (m := D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening.absWord [a,b,a+b,a-b,c,d,e])
    (d := 7) rfl rfl
  exact (homogeneousSubmodule (Fin 9) K 7).smul_mem _
    ((homogeneousSubmodule (Fin 9) K 7).smul_mem _
      ((homogeneousSubmodule (Fin 9) K 7).smul_mem _ (grade_mem.mp hw).1))

private theorem literalF11_grade : F11 ∈ grade 7 11 := by
  apply grade_mem.mpr
  refine ⟨?_, weightedHomogeneousComponent_isWeightedHomogeneous _ _⟩
  rw [literalF11_field_sum]
  apply IsHomogeneous.sum
  intro a _
  apply IsHomogeneous.sum
  intro b _
  apply IsHomogeneous.sum
  intro c _
  apply IsHomogeneous.sum
  intro d _
  apply IsHomogeneous.sum
  intro e _
  split_ifs
  · exact signedProduct_homogeneous _ _ _ _ _
  · exact isHomogeneous_zero (σ := Fin 9) (R := K) 7

theorem literalF11_eigengrade : q F11 ∈ eigengrade 7 11 := by
  refine eigengrade_mem.mpr ⟨⟨F11, literalF11_grade,rfl⟩, ?_⟩
  rw [Tbar_q, literalF11_character, map_smul]

end D5.S3.Arith.Partitions.BilgiciThetaStructural

open D5.S3.Arith.Partitions.BilgiciThetaQuartic hiding digit
open MvPolynomial
open scoped BigOperators

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural
open D5.S3.Arith.Partitions.BilgiciThetaStructural.Straightening (digit absIndex epsilon epsilon_abs x x_digit x_abs raw)

private theorem eta_signed_word (l : List K) :
    eta (raw l) = dual l.prod (l.prod * (l.map (· ^ 4)).sum) := by
  induction l with
  | nil => simp [raw]; rfl
  | cons a l ih =>
    change eta (x a * raw l) = dual (a * l.prod) (a * l.prod * (a^4 + (l.map (· ^ 4)).sum))
    rw [map_mul, eta_signed_index, ih]
    apply TrivSqZeroExt.ext
    · rfl
    · rw [TrivSqZeroExt.snd_mul (R := K) (M := K)]
      simp only [dual, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk, op_smul_eq_mul,
        smul_eq_mul]
      ring

private theorem finite_field_moment {p : MvPolynomial (Fin 5) K} (h : p.totalDegree < 90) :
    ∑ f : Fin 5 → K, eval f p = 0 := by
  classical
  rw [← support_sum_monomial_coeff p]
  simp only [map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro n hn
  have hd := le_totalDegree hn
  have hsmall : ∃ i : Fin 5, n i < 18 := by
    by_contra! hc
    have h90 : 90 ≤ ∑ i : Fin 5, n i := by
      calc
        90 = ∑ _ : Fin 5, (18 : ℕ) := by simp
        _ ≤ _ := Finset.sum_le_sum (fun i _ => hc i)
    have hs : (n.sum fun _ e => e) = ∑ i : Fin 5, n i :=
      Finsupp.sum_fintype _ _ (fun _ => rfl)
    omega
  obtain ⟨i, hi⟩ := hsmall
  simp only [eval_monomial]
  have he (f : Fin 5 → K) :
      n.prod (fun j e => f j ^ e) = ∏ j, f j ^ n j :=
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)
  simp only [he, ← Finset.mul_sum]
  have hf := Fintype.prod_sum (fun j (a : K) => a ^ n j)
  rw [← hf]
  have hz : ∑ a : K, a ^ n i = 0 :=
    FiniteField.sum_pow_lt_card_sub_one K (n i) (by exact hi)
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hz, mul_zero]

private theorem totalDegree_sub_le {p q : MvPolynomial (Fin 5) K} :
    (p - q).totalDegree ≤ max p.totalDegree q.totalDegree := by
  rw [sub_eq_add_neg]
  refine (totalDegree_add ..).trans (max_le_max_left _ ?_)
  rw [← neg_one_smul K q]
  exact totalDegree_smul_le _ _

private theorem bounded_list_prod {ps : List (MvPolynomial (Fin 5) K)}
    (h : ∀ p ∈ ps, p.totalDegree ≤ 1) : ps.prod.totalDegree ≤ ps.length := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    rw [List.prod_cons, List.length_cons]
    have hp := h p (by simp)
    have hq := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have hmul := totalDegree_mul p ps.prod
    omega

private theorem bounded_list_fourth_sum {ps : List (MvPolynomial (Fin 5) K)}
    (h : ∀ p ∈ ps, p.totalDegree ≤ 1) :
    ((ps.map (· ^ 4)).sum).totalDegree ≤ 4 := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons]
    have hp := h p (by simp)
    have hq := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    exact (totalDegree_add ..).trans (max_le
      ((totalDegree_pow p 4).trans (by omega)) hq)

private noncomputable def momentPoly : MvPolynomial (Fin 5) K :=
  let a := X 0
  let b := X 1
  let c := X 2
  let d := X 3
  let e := X 4
  let l : List (MvPolynomial (Fin 5) K) := [a,b,a+b,a-b,c,d,e]
  (1 - (C 3*(a^2+b^2)+c^2+d^2+e^2)^18) *
    (C (3/8) * a * b * (b^2-a^2) * c * d * e) *
    l.prod * (l.map (· ^ 4)).sum

private theorem add_degree {p q : MvPolynomial (Fin 5) K} {n : ℕ}
    (hp : p.totalDegree ≤ n) (hq : q.totalDegree ≤ n) : (p+q).totalDegree ≤ n :=
  (totalDegree_add ..).trans (max_le hp hq)

private theorem mul_degree {p q : MvPolynomial (Fin 5) K} {m n : ℕ}
    (hp : p.totalDegree ≤ m) (hq : q.totalDegree ≤ n) : (p*q).totalDegree ≤ m+n :=
  (totalDegree_mul ..).trans (Nat.add_le_add hp hq)

private theorem pow_degree {p : MvPolynomial (Fin 5) K} {m : ℕ}
    (hp : p.totalDegree ≤ m) (n : ℕ) : (p^n).totalDegree ≤ n*m :=
  (totalDegree_pow ..).trans (Nat.mul_le_mul_left _ hp)

set_option maxHeartbeats 1000000 in
private theorem moment_degree : momentPoly.totalDegree ≤ 54 := by
  let a : MvPolynomial (Fin 5) K := X 0
  let b : MvPolynomial (Fin 5) K := X 1
  let c : MvPolynomial (Fin 5) K := X 2
  let d : MvPolynomial (Fin 5) K := X 3
  let e : MvPolynomial (Fin 5) K := X 4
  let l := [a,b,a+b,a-b,c,d,e]
  change ((1 - (C 3*(a^2+b^2)+c^2+d^2+e^2)^18) *
    (C (3/8) * a * b * (b^2-a^2) * c * d * e) *
    l.prod * (l.map (· ^ 4)).sum).totalDegree ≤ 54
  have ha : a.totalDegree ≤ 1 := (totalDegree_X 0).le
  have hb : b.totalDegree ≤ 1 := (totalDegree_X 1).le
  have hc : c.totalDegree ≤ 1 := (totalDegree_X 2).le
  have hd : d.totalDegree ≤ 1 := (totalDegree_X 3).le
  have he : e.totalDegree ≤ 1 := (totalDegree_X 4).le
  have hlabels : ∀ p ∈ l, p.totalDegree ≤ 1 := by
    intro p hp
    simp only [l, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact add_degree ha hb
    · exact totalDegree_sub_le.trans (max_le ha hb)
    · exact hc
    · exact hd
    · exact he
  have hcenter : (C 3*(a^2+b^2)+c^2+d^2+e^2).totalDegree ≤ 2 :=
    add_degree (add_degree (add_degree
      (mul_degree (totalDegree_C (3 : K)).le (add_degree (pow_degree ha 2) (pow_degree hb 2)))
      (pow_degree hc 2)) (pow_degree hd 2)) (pow_degree he 2)
  have hf : (1 - (C 3*(a^2+b^2)+c^2+d^2+e^2)^18).totalDegree ≤ 36 :=
    totalDegree_sub_le.trans (max_le (totalDegree_one.trans_le (Nat.zero_le _))
      (pow_degree hcenter 18))
  have hab : (b^2-a^2).totalDegree ≤ 2 :=
    totalDegree_sub_le.trans (max_le (pow_degree hb 2) (pow_degree ha 2))
  have hcoeff : (C (3/8) * a * b * (b^2-a^2) * c * d * e).totalDegree ≤ 7 :=
    mul_degree (mul_degree (mul_degree (mul_degree (mul_degree (mul_degree
      (totalDegree_C (3/8 : K)).le ha) hb) hab) hc) hd) he
  have hp : l.prod.totalDegree ≤ 7 := bounded_list_prod hlabels
  exact mul_degree (mul_degree (mul_degree hf hcoeff) hp) (bounded_list_fourth_sum hlabels)

private theorem weight_indicator (z : K) : (if z = 0 then (1 : K) else 0) = 1 - z^18 := by
  split_ifs with h
  · simp [h]
  · rw [show z^18 = 1 from ZMod.pow_card_sub_one_eq_one h, sub_self]

set_option maxHeartbeats 1000000 in
private theorem moment_eval (f : Fin 5 → K) :
    eval f momentPoly =
      epsR (if centerOf (f 0) (f 1) (f 2) (f 3) (f 4) = 0 then
        signedProduct (f 0) (f 1) (f 2) (f 3) (f 4) else 0) := by
  let a := f 0
  let b := f 1
  let c := f 2
  let d := f 3
  let e := f 4
  let l := [a,b,a+b,a-b,c,d,e]
  have h (z : K) (r : R) : epsR (if z = 0 then r else 0) =
      (if z = 0 then 1 else 0 : K) * epsR r := by split_ifs <;> simp
  change _ = epsR (if centerOf a b c d e = 0 then signedProduct a b c d e else 0)
  rw [h, weight_indicator, signedProduct_word, map_smul]
  have hw : epsR (raw l) = l.prod * (l.map (· ^ 4)).sum := by
    change (eta (raw l)).snd = _
    rw [eta_signed_word]
    rfl
  change _ = (1 - centerOf a b c d e ^ 18) *
    (((3/8 : K)*a*b*(b^2-a^2)*c*d*e) • epsR (raw l))
  rw [hw, smul_eq_mul]
  simp only [momentPoly, map_mul, map_add, map_sub, map_one, map_pow, eval_C, eval_X,
    List.prod_cons, List.prod_nil, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  change (1 - centerOf a b c d e ^ 18) * _ * l.prod * _ = _
  simp only [l,a,b,c,d,e,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ac_rfl

private theorem sum_fin_cons {M : Type*} [AddCommMonoid M] (n : ℕ) (f : (Fin (n+1) → K) → M) :
    ∑ a : K, ∑ u : Fin n → K, f (Fin.cons a u) = ∑ v : Fin (n+1) → K, f v := by
  let s := Fin.consEquiv (fun _ : Fin (n+1) => K)
  calc
    _ = ∑ p : K × (Fin n → K), f (s p) := (Fintype.sum_prod_type (fun p => f (s p))).symm
    _ = _ := Equiv.sum_comp s f

private theorem sum_field_five {M : Type*} [AddCommMonoid M] (f : (Fin 5 → K) → M) :
    (∑ u : Fin 5 → K, f u) = ∑ a : K, ∑ b : K, ∑ c : K, ∑ d : K, ∑ e : K, f ![a,b,c,d,e] := by
  refine (sum_fin_cons 4 f).symm.trans ?_
  apply Finset.sum_congr rfl
  intro a _
  refine (sum_fin_cons 3 (fun u => f (Fin.cons a u))).symm.trans ?_
  apply Finset.sum_congr rfl
  intro b _
  refine (sum_fin_cons 2 (fun u => f (Fin.cons a (Fin.cons b u)))).symm.trans ?_
  apply Finset.sum_congr rfl
  intro c _
  refine (sum_fin_cons 1 (fun u => f (Fin.cons a (Fin.cons b (Fin.cons c u))))).symm.trans ?_
  apply Finset.sum_congr rfl
  intro d _
  refine (sum_fin_cons 0 (fun u => f (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d u)))))).symm.trans ?_
  apply Finset.sum_congr rfl
  intro e _
  rw [Fintype.sum_subsingleton _ (Fin.elim0 : Fin 0 → K)]
  apply congrArg f
  funext i
  fin_cases i <;> rfl

theorem literalF11_epsilon_zero : eps (q F11) = 0 := by
  rw [eps_q, literalF11_field_sum]
  simp only [map_sum]
  have hm := finite_field_moment (p := momentPoly) (by have := moment_degree; omega)
  rw [sum_field_five] at hm
  refine Eq.trans ?_ hm
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  exact (moment_eval ![a,b,c,d,e]).symm

end D5.S3.Arith.Partitions.BilgiciThetaStructural

open D5.S3.Arith.Partitions.BilgiciThetaQuartic hiding digit
open MvPolynomial
open scoped BigOperators

namespace D5.S3.Arith.Partitions.BilgiciThetaStructural

private def traceHead (n : ℕ) (p : Sparse) : Sparse :=
  p.filter fun t => decide (traceDegree t.1 = n)

private def traceAtLeast (n : ℕ) (p : Sparse) : Prop :=
  ∀ t ∈ p, n ≤ traceDegree t.1

private theorem traceDegree_times (a b : Word × K) :
    traceDegree (timesTerm a b).1 =
      traceDegree a.1 + traceDegree b.1 := by
  change traceDegree (sortWord (a.1 ++ b.1)) = _
  unfold traceDegree;
  unfold sortWord;
  rw [((List.perm_insertionSort (· ≤ ·) (a.1 ++ b.1)).map tNatural).sum_eq,
    List.map_append, List.sum_append]

private theorem traceAtLeast_rawMul {m n : ℕ} {p r : Sparse}
    (hp : traceAtLeast m p) (hr : traceAtLeast n r) :
    traceAtLeast (m+n) (rawMul p r) := by
  intro t ht
  change t ∈ p.flatMap (fun a => r.map (timesTerm a)) at ht
  obtain ⟨a, ha, h⟩ := List.mem_flatMap.mp ht
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
  rw [traceDegree_times]
  exact Nat.add_le_add (hp a ha) (hr b hb)

private theorem traceHead_rawMul {m n : ℕ} {p r : Sparse}
    (hp : traceAtLeast m p) (hr : traceAtLeast n r) :
    traceHead (m+n) (rawMul p r) =
      rawMul (traceHead m p) (traceHead n r) := by
  have he (a : Word × K) (ha : a ∈ p) (b : Word × K) (hb : b ∈ r) :
      decide (traceDegree (timesTerm a b).1 = m+n) =
        (decide (traceDegree a.1 = m) && decide (traceDegree b.1 = n)) := by
    rw [traceDegree_times]
    have ha' := hp a ha
    have hb' := hr b hb
    by_cases h₁ : traceDegree a.1 = m <;>
      by_cases h₂ : traceDegree b.1 = n
    · simp [h₁, h₂]
    all_goals
      have hne : traceDegree a.1 + traceDegree b.1 ≠ m+n := by omega
      simp [h₁,h₂,hne]
  induction p with
  | nil => rfl
  | cons a p ih =>
    have hp' : traceAtLeast m p := fun t ht => hp t (List.mem_cons_of_mem _ ht)
    have ih' := ih hp' (fun t ht => he t (List.mem_cons_of_mem _ ht))
    have htail := he a (List.mem_cons_self ..)
    unfold rawMul;
    unfold traceHead
    simp only [List.flatMap_cons, List.filter_append, List.filter_cons]
    change _ ++ traceHead (m+n) (rawMul p r) = _
    rw [ih']
    by_cases ha : traceDegree a.1 = m
    · simp only [ha, decide_true, ite_true, List.flatMap_cons]
      congr 1
      rw [List.filter_map]
      apply congrArg (List.map (timesTerm a))
      apply List.filter_congr
      intro b hb
      simpa [ha] using htail b hb
    · simp only [ha, decide_false]
      have hz : List.filter (fun t => decide (traceDegree t.1 = m+n))
          (r.map (timesTerm a)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro t ht
        obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ht
        simp only [htail b hb, ha, decide_false, Bool.false_and]
        decide
      rw [hz, List.nil_append]
      rfl

private theorem traceCoeff_head (n : ℕ) (p : Sparse) :
    traceCoeff n p = ((traceHead n p).map Prod.snd).sum := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    obtain ⟨m,c⟩ := t
    change ((if traceDegree m = n then c else 0) + traceCoeff n p) =
      ((traceHead n ((m,c) :: p)).map Prod.snd).sum
    by_cases h : traceDegree m = n
    · simp [traceHead, h, ih]
    · simp [traceHead, h, ih]

private def productTerms : Sparse :=
  rawMul (rawMul (rawMul
    fullB fullC) fullC) fullC

private def takeWeight (p : Sparse) : Sparse :=
  p.filter fun t => decide ((11 : K) = wordWeight t.1)

private theorem denote_traceF11 :
    denote (takeWeight productTerms) = F11 := by
  unfold takeWeight
  rw [denote_component]
  simp only [F11, productTerms, denote_rawMul, denote_fullB,
    denote_fullC, pow_succ', pow_zero, mul_one]
  ring

private theorem B_order : traceAtLeast 30 fullB := by
  unfold traceAtLeast
  decide
private theorem C_order : traceAtLeast 0 fullC := by
  intro t ht
  exact Nat.zero_le _
private theorem B_bottom : traceHead 30 fullB =
    [([2,5,6,8], (1 : K))] := by decide
private theorem C_bottom : traceHead 0 fullC = [([8], (1 : K))] := by decide

private theorem product_order : traceAtLeast 30 productTerms :=
  traceAtLeast_rawMul (traceAtLeast_rawMul (traceAtLeast_rawMul B_order C_order) C_order) C_order

private theorem product_bottom : traceHead 30 productTerms =
    [([2,5,6,8,8,8,8], (1 : K))] := by
  have h1 := traceAtLeast_rawMul B_order C_order
  have h2 := traceAtLeast_rawMul h1 C_order
  unfold productTerms
  rw [traceHead_rawMul h2 C_order, traceHead_rawMul h1 C_order, traceHead_rawMul B_order C_order,
    B_bottom, C_bottom]
  decide

private theorem literalF11_trace_low (n : ℕ) (hn : n < 30) : ellR n F11 = 0 := by
  rw [← denote_traceF11, ellR_sparse, traceCoeff_head]
  have hhead : traceHead n (takeWeight productTerms) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    have h := product_order t (List.mem_filter.mp ht).1
    have hh : traceDegree t.1 ≠ n := by omega
    simp [hh]
  rw [hhead]
  rfl

theorem literalF11_trace_thirty : ellR 30 F11 = 1 := by
  rw [← denote_traceF11, ellR_sparse, traceCoeff_head]
  have hcomm : traceHead 30 (takeWeight productTerms) = takeWeight (traceHead 30 productTerms) := by
    simp only [takeWeight, traceHead, List.filter_filter, Bool.and_comm]
  rw [hcomm, product_bottom]
  decide

theorem literalF11_trace_test_zero : ell 11 (by decide) (q F11) = 0 := by
  rw [ell_q]
  exact literalF11_trace_low 11 (by decide)

theorem literalF11_class_nonzero : q F11 ≠ 0 := by
  intro hz
  have h := congrArg (ell 30 (by decide)) hz
  rw [ell_q, literalF11_trace_thirty, map_zero] at h
  exact one_ne_zero h

end D5.S3.Arith.Partitions.BilgiciThetaStructural

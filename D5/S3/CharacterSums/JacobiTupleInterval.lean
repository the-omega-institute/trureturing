/- GID: D5/S3/CharacterSums/JacobiTupleInterval
   generality: I
   mirror-B: D5/B/S3/CharacterSums/JacobiTupleInterval
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Repeated prime Jacobi tuples have an explicit incomplete-period discrepancy, and full affine power moments reindex as moments of independent signed quadratic coordinates. -/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Tactic

set_option autoImplicit false
open Finset
noncomputable section

namespace D5.S3.CharacterSums.JacobiTupleInterval

/-- Product of Jacobi rows, with the tuple retaining repeated prime factors. -/
def row {k : ℕ} (f : Fin k → ℕ) (b m i : ℕ) : ℝ :=
  ∏ j, (jacobiSym (f j : ℤ) (b+m*i) : ℝ)

/-- Sum over consecutive indices starting at A. -/
def block (g : ℕ → ℝ) (A L : ℕ) : ℝ := ∑ i ∈ range L, g (A+i)

private lemma shift_full (g : ℕ → ℝ) (R : ℕ) (hper : ∀ i, g (i+R)=g i) (A : ℕ) :
    block g A R = block g 0 R := by
  induction A with
  | zero => rfl
  | succ A ih =>
    have hs := Finset.sum_range_succ' (fun i => g (A+i)) R
    rw [Finset.sum_range_succ] at hs
    simp only [Nat.add_zero,hper] at hs
    calc
      block g (A+1) R = block g A R := by
        unfold block
        simpa [Nat.add_assoc, Nat.add_comm 1] using (add_right_cancel hs.symm)
      _ = _ := ih

private lemma periodic_mean (g : ℕ → ℝ) {R Q : ℕ} (hR : 0 < R) (hQ : 0 < Q) (hd : R ∣ Q)
    (hper : ∀ i, g (i+R)=g i) (hb : ∀ i, |g i| ≤ 1) (A L : ℕ) :
    |block g A L - (L:ℝ) * (block g 0 Q / Q)| ≤ 2*(L % R : ℕ) := by
  have hm (A l : ℕ) : block g A (R*l) = (l:ℝ)*block g 0 R := by
    induction l with
    | zero => simp [block]
    | succ l ih =>
      rw [Nat.mul_succ,block,Finset.sum_range_add]
      change block g A (R*l) + _ = _
      rw [ih]
      have he := shift_full g R hper (A+R*l)
      simp only [block,Nat.add_assoc] at he
      rw [he, Nat.cast_succ, add_mul, one_mul]
      rfl
  obtain ⟨s,hs⟩ := hd
  have hQr : (Q:ℝ)≠0 := by exact_mod_cast hQ.ne'
  have hRr : (R:ℝ)≠0 := by exact_mod_cast hR.ne'
  have he : block g 0 Q / Q = block g 0 R / R := by
    rw [eq_div_iff hRr, div_mul_eq_mul_div, div_eq_iff hQr, hs, hm, Nat.cast_mul]
    ring
  have hab (a l : ℕ) : |block g a l| ≤ (l:ℝ) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa using Finset.sum_le_card_nsmul (range l) (fun i => |g (a+i)|) 1 (fun i _ => hb _)
  have hmean : |block g 0 R / R| ≤ 1 := by
    rw [abs_div,(abs_of_nonneg (Nat.cast_nonneg R) : |(R:ℝ)| = R), div_le_one (by exact_mod_cast hR)]
    exact hab _ _
  have hdiv := Nat.div_add_mod L R
  have hpart : block g A L = (L / R : ℕ) * block g 0 R + block g (A+R*(L/R)) (L%R) := by
    conv_lhs => rw [← hdiv, block, Finset.sum_range_add]
    rw [← hm A (L/R)]
    simp [block,Nat.add_assoc]
  have hcast := congrArg (fun n : ℕ => (n:ℝ)) hdiv
  push_cast at hcast
  have herr : block g A L - (L:ℝ) * (block g 0 Q / Q) =
      block g (A+R*(L/R)) (L%R) - (L%R : ℕ)*(block g 0 R/R) := by
    rw [hpart,he]
    field_simp
    linear_combination block g 0 R * hcast
  rw [herr]
  apply (abs_sub _ _).trans
  rw [abs_mul, (abs_of_nonneg (Nat.cast_nonneg (L%R)) : |((L%R:ℕ):ℝ)| = _)]
  nlinarith [hab (A+R*(L/R)) (L%R), mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg (L%R) : (0:ℝ)≤_)]

/-- Discrepancy against the complete primorial mean for an arbitrary tuple, with repetitions. -/
theorem tuple_interval_mean {k : ℕ} (P : Finset ℕ) (f : Fin k → ℕ) (hf : ∀ j, f j ∈ P)
    (hp : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (b m A L : ℕ) (hb : b%4=3) (hm : 4 ∣ m) :
    let Q := ∏ p ∈ P, p
    |block (row f b m) A L - (L:ℝ) * (block (row f b m) 0 Q / Q)| ≤ 2 * (∏ j, (f j : ℝ)) := by
  classical
  let S := univ.image f
  let R := ∏ p ∈ S, p
  let Q := ∏ p ∈ P, p
  have hsub : S ⊆ P := by
    intro p hp
    obtain ⟨j,_,rfl⟩ := mem_image.mp hp
    exact hf j
  have hR : 0 < R := Finset.prod_pos (fun p h => (hp _ (hsub h)).1.pos)
  have hQ : 0 < Q := Finset.prod_pos (fun p h => (hp _ h).1.pos)
  have hd : R ∣ Q := Finset.prod_dvd_prod_of_subset S P id hsub
  have hper (i : ℕ) : row f b m (i+R) = row f b m i := by
    unfold row
    apply Finset.prod_congr rfl
    intro j _
    have hpR : f j ∣ R := Finset.dvd_prod_of_mem id (mem_image.mpr ⟨j,mem_univ _,rfl⟩)
    have hfour (u : ℕ) : (b+m*u)%4=3 := by
      rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hm _),Nat.add_zero,Nat.mod_mod,hb]
    have hh (u : ℕ) := jacobiSym.quadratic_reciprocity_if (Nat.odd_iff.mp ((hp _ (hf j)).1.odd_of_ne_two (hp _ (hf j)).2))
      (show (b+m*u)%2=1 by have := hfour u; omega)
    have hn : b+m*(i+R) ≡ b+m*i [MOD f j] := by
      rw [Nat.mul_add]
      exact (Nat.ModEq.add_left _ ((Nat.modEq_zero_iff_dvd.2 (dvd_mul_of_dvd_right hpR m)).add_left _))
    have hj := jacobiSym.mod_left' (Int.natCast_modEq_iff.2 hn)
    rw [← hh (i+R),← hh i,hfour,hfour,hj]
  have hbound (i : ℕ) : |row f b m i| ≤ 1 := by
    rw [row,Finset.abs_prod]
    apply Finset.prod_le_one₀
    · intro j _; positivity
    · intro j _
      rcases jacobiSym.trichotomy (f j:ℤ) (b+m*i) with h|h|h <;> norm_num [h]
  have hprod : R ≤ ∏ j, f j := Finset.prod_image_le_of_one_le (f := id) (fun p h => (hp _ (hsub h)).1.one_le)
  have h := periodic_mean (row f b m) hR hQ hd hper hbound A L
  refine h.trans ?_
  exact_mod_cast Nat.mul_le_mul_left 2 ((Nat.mod_lt L hR).le.trans hprod)


/-- Signed quadratic character incorporating the fixed reciprocity sign of d = 3 modulo 4. -/
def coordinate {p : ℕ} (hp : p.Prime) (z : ZMod p) : ℝ := by
  let _ : Fact p.Prime := ⟨hp⟩
  exact (if p%4 = 3 then (-1:ℝ) else 1) * quadraticChar (ZMod p) z

private lemma fin_cast_crt {t : ℕ} [NeZero t] (i : Fin t) : ZMod.finEquiv t i = (i.val : ZMod t) := by
  cases t with
  | zero => exact Fin.elim0 i
  | succ t => exact (Fin.cast_val_eq_self i).symm

/-- An affine complete moment equals the independent finite-field moment of signed characters. -/
theorem affine_complete_crt (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime ∧ p≠2)
    (b m A ell : ℕ) (hb : b%4=3) (hm : 4∣m) (hc : ∀ p ∈ P, m.Coprime p)
    (a : P → ℝ) :
    letI : ∀ p : P, NeZero (p : ℕ) := fun p => ⟨(hp p p.2).1.ne_zero⟩
    (∑ i ∈ range (∏ p ∈ P,p), (∑ p : P, a p * (jacobiSym (p:ℤ) (b+m*(A+i)) : ℝ))^ell) =
      ∑ z : ((p : P) → ZMod (p:ℕ)), (∑ p : P, a p * coordinate (hp p p.2).1 (z p))^ell := by
  classical
  let _ : ∀ p : P, NeZero (p : ℕ) := fun p => ⟨(hp p p.2).1.ne_zero⟩
  let Q := ∏ p : P, (p:ℕ)
  have hQ : 0 < Q := Finset.prod_pos (fun p _ => (hp p p.2).1.pos)
  let _ : NeZero Q := ⟨hQ.ne'⟩
  have co : Pairwise (fun p r : P => Nat.Coprime (p:ℕ) (r:ℕ)) := by
    intro p r hn
    exact (Nat.coprime_primes (hp p p.2).1 (hp r r.2).1).2 (fun h => hn (Subtype.ext h))
  let e := ZMod.prodEquivPi (fun p : P => (p:ℕ)) co
  have hmQ : m.Coprime Q := Nat.coprime_prod_right_iff.mpr (fun p _ => hc p p.2)
  let u := ((ZMod.isUnit_iff_coprime m Q).2 hmQ).unit
  have hu : (u : ZMod Q) = m := IsUnit.unit_spec _
  let perm := (((((ZMod.finEquiv Q).toEquiv.trans (Equiv.addLeft (A : ZMod Q))).trans
    (Units.mulLeft u)).trans (Equiv.addLeft (b : ZMod Q))).trans e.toEquiv)
  let F (z : (p : P) → ZMod (p:ℕ)) : ℝ := (∑ p : P, a p * coordinate (hp p p.2).1 (z p))^ell
  have hw (i : Fin Q) (p : P) : (jacobiSym (p:ℤ) (b+m*(A+i.val)) : ℝ) =
      coordinate (hp p p.2).1 (perm i p) := by
    let _ : Fact (p:ℕ).Prime := ⟨(hp p p.2).1⟩
    have hfour : (b+m*(A+i.val))%4=3 := by
      rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hm _),Nat.add_zero,Nat.mod_mod,hb]
    have hsym := jacobiSym.quadratic_reciprocity_if (Nat.odd_iff.mp ((hp p p.2).1.odd_of_ne_two (hp p p.2).2))
      (show (b+m*(A+i.val))%2=1 by omega)
    have hperm : perm i p = ((b+m*(A+i.val) : ℕ) : ZMod (p:ℕ)) := by
      change e ((b : ZMod Q) + (u : ZMod Q)*((A : ZMod Q) + ZMod.finEquiv Q i)) p = _
      rw [hu,fin_cast_crt,← Nat.cast_add,← Nat.cast_mul,← Nat.cast_add,map_natCast]
      rfl
    rw [hperm,← hsym,hfour, ← jacobiSym.legendreSym.to_jacobiSym]
    by_cases h : (p:ℕ)%4=3 <;> simp [h,coordinate, legendreSym]
  have hprod : Q = ∏ p ∈ P,p := Finset.prod_coe_sort P id
  rw [← hprod, ← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i : Fin Q, F (perm i) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact Finset.sum_congr rfl (fun p _ => congrArg (a p * ·) (hw i p))
    _ = _ := perm.sum_comp F

/-- The signed prime coordinate has values in the three-point set and zero total sum. -/
theorem coordinate_laws (p : ℕ) (hp : p.Prime) (ho : p ≠ 2) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    (∀ z : ZMod p, coordinate hp z = -1 ∨ coordinate hp z = 0 ∨ coordinate hp z = 1) ∧
      ∑ z : ZMod p, coordinate hp z = 0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  constructor
  · intro z
    have hj := jacobiSym.trichotomy (z.val : ℤ) p
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast, ZMod.natCast_zmod_val] at hj
    by_cases h : p%4=3 <;> rcases hj with g|g|g <;> simp [coordinate,h,g]
  · have hz := quadraticChar_sum_zero (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
    simp only [coordinate,← Finset.mul_sum,← Int.cast_sum,hz,Int.cast_zero,mul_zero]

end D5.S3.CharacterSums.JacobiTupleInterval

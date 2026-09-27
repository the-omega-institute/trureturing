/- GID: D5/S3/Arith/Covering/CriticalCosetObstruction
   generality: I
   mirror-B: D5/B/S3/Arith/Covering/CriticalCosetObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Nullstellensatz]
   utility: kind=numeric-reduction; basis=refutes=gid:D5/S3/Arith/Covering/CriticalCosetObstruction.claim; result=D5/S3/Arith/Covering/CriticalCosetObstruction.result; claim=D5/S3/Arith/Covering/CriticalCosetObstruction.claim
   digest: The original 33 rows leave twelve holes in every critical coset for all fixed phases. -/

import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Order.Interval.Finset.Fin
namespace D5.S3.Arith.Covering.CriticalCosetObstruction

noncomputable section
open scoped BigOperators
open MvPolynomial
abbrev F := ZMod 23
structure Row where
  p : ℤ
  e : ℤ
  a : ℤ
  b : ℤ
/-- Prime, modulus and unreduced integer normal from each selected original row. -/
def rows : Fin 33 → Row := ![
  ⟨47, 23, 9, 10⟩,
  ⟨139, 138, 1, 41⟩,
  ⟨277, 276, 147, 188⟩,
  ⟨461, 460, 1, 111⟩,
  ⟨599, 299, 131, 201⟩,
  ⟨691, 690, 591, 1⟩,
  ⟨829, 828, 1, 376⟩,
  ⟨967, 966, 374, 237⟩,
  ⟨1013, 1012, 363, 1⟩,
  ⟨1151, 575, 214, 401⟩,
  ⟨1289, 1288, 1016, 273⟩,
  ⟨1381, 1380, 1, 292⟩,
  ⟨1657, 828, 171, 532⟩,
  ⟨1933, 644, 521, 566⟩,
  ⟨2347, 2346, 2223, 1⟩,
  ⟨2393, 2392, 196, 1⟩,
  ⟨2531, 2530, 1, 262⟩,
  ⟨3037, 3036, 1, 1126⟩,
  ⟨3221, 644, 627, 493⟩,
  ⟨3313, 1656, 422, 935⟩,
  ⟨3727, 3726, 380, 1⟩,
  ⟨3911, 1955, 898, 264⟩,
  ⟨4049, 4048, 3272, 1⟩,
  ⟨4831, 4830, 2378, 1⟩,
  ⟨4969, 2484, 2285, 2364⟩,
  ⟨5521, 2760, 2303, 2418⟩,
  ⟨6073, 3036, 1811, 2908⟩,
  ⟨7177, 3588, 2285, 834⟩,
  ⟨9109, 3036, 2605, 2486⟩,
  ⟨12421, 4140, 163, 3364⟩,
  ⟨44851, 3450, 41, 1579⟩,
  ⟨71761, 4485, 3348, 74⟩,
  ⟨109297, 3036, 795, 2941⟩]
def normal (i : Fin 33) : MvPolynomial Bool F :=
  C ((rows i).a : F) * X false + C ((rows i).b : F) * X true
def topIndex : Bool →₀ ℕ := Finsupp.single false 22 + Finsupp.single true 11

def fieldHoles (offset : Fin 33 → F) (active : Finset (Fin 33)) : Finset (F × F) :=
  Finset.univ.filter fun z => ∀ i ∈ active, (rows i).a * z.1 + (rows i).b * z.2 ≠ offset i
/-- Every choice of offsets and active rows leaves at least twelve field points.
The top coefficient is computed from the literal original integer normals. -/
theorem affine_holes (offset : Fin 33 → F) (active : Finset (Fin 33)) :
    12 ≤ (fieldHoles offset active).card := by
  classical
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  have hc : coeff topIndex (∏ i, normal i) = 1 := by
    unfold normal rows
    simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.prod_univ_zero, mul_one]
    norm_num [map_intCast, map_ofNat]
    conv_lhs => arg 2; ring_nf
    simp only [← map_ofNat C, X_pow_eq_monomial]
    have hcm (s : Bool →₀ ℕ) (r t : F) :
        monomial s r * C t = monomial s (r * t) := by
      rw [mul_comm, C_mul_monomial, mul_comm]
    simp only [X, monomial_mul, hcm, coeff_add, coeff_monomial]
    norm_num [topIndex, Finsupp.ext_iff, Bool.forall_bool]
    decide +kernel
  let f (i : Fin 33) := normal i - C (offset i)
  have hn (i : Fin 33) : (normal i).totalDegree ≤ 1 := by
    unfold normal
    apply (totalDegree_add _ _).trans
    apply max_le
    all_goals
      apply (totalDegree_mul _ _).trans
      simp only [totalDegree_C, totalDegree_X, zero_add, le_refl]
  have hf (i : Fin 33) : (f i).totalDegree ≤ 1 :=
    (totalDegree_sub_C_le _ _).trans (hn i)
  have hp (s : Finset (Fin 33)) (g : Fin 33 → MvPolynomial Bool F)
      (hg : ∀ i, (g i).totalDegree ≤ 1) : (s.prod g).totalDegree ≤ s.card := by
    apply (totalDegree_finsetProd s g).trans
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ s) => hg i)
  have herr : (∑ i : Fin 33, C (offset i) *
      (∏ j ∈ Finset.univ.filter (· < i), f j) *
      ∏ j ∈ Finset.univ.filter (i < ·), normal j).totalDegree ≤ 32 := by
    apply totalDegree_finsetSum_le
    intro i _
    apply (totalDegree_mul _ _).trans
    have hleft := totalDegree_mul (C (offset i))
      (∏ j ∈ Finset.univ.filter (· < i), f j)
    have hp₁ := hp (Finset.univ.filter (· < i)) f hf
    have hp₂ := hp (Finset.univ.filter (i < ·)) normal hn
    simp only [totalDegree_C, zero_add] at hleft
    simp only [Finset.filter_gt_eq_Iio, Finset.filter_lt_eq_Ioi,
      Fin.card_Iio, Fin.card_Ioi] at hp₁ hp₂ hleft ⊢
    have := i.isLt
    omega
  have ht : topIndex.degree = 33 := by simp [topIndex, map_add]
  have ht' : (topIndex.sum fun _ n => n) = 33 := by
    simpa only [Finsupp.degree_apply, Finsupp.sum] using ht
  have hcoeff : coeff topIndex (∏ i, f i) = 1 := by
    dsimp [f]
    rw [Finset.prod_sub_ordered, coeff_sub, hc]
    have hz := coeff_eq_zero_of_totalDegree_lt
      (lt_of_le_of_lt herr (by change 32 < topIndex.sum (fun _ n => n); rw [ht']; decide))
    simpa [f] using congrArg (fun x : F => 1 - x) hz
  have hd : (∏ i, f i).totalDegree = topIndex.degree := by
    apply Nat.le_antisymm
    · simpa [ht] using hp Finset.univ f hf
    · have hmem : topIndex ∈ (∏ i, f i).support := by simp [mem_support_iff, hcoeff]
      simpa only [Finsupp.degree_apply, Finsupp.sum] using le_totalDegree hmem
  by_contra! hsmall
  let ys := (fieldHoles offset active).image Prod.snd
  let S : Bool → Finset F := fun b => if b then Finset.univ \ ys else Finset.univ
  have hys : ys.card ≤ 11 := by
    have hi := Finset.card_image_le (s := fieldHoles offset active) (f := Prod.snd)
    dsimp [ys]
    omega
  have hS : ∀ b, topIndex b < (S b).card := by
    intro b
    cases b
    · norm_num [S, topIndex, ZMod.card]
    · have he := Finset.card_sdiff_of_subset (Finset.subset_univ ys)
      simp only [Finset.card_univ, ZMod.card] at he
      simp only [S, ↓reduceIte, topIndex, Finsupp.add_apply,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide : true ≠ false), zero_add]
      omega
  obtain ⟨z, hz, hne⟩ := combinatorial_nullstellensatz_exists_eval_nonzero
    (∏ i, f i) topIndex (by rw [hcoeff]; exact one_ne_zero) hd S hS
  have hhole : (z false, z true) ∈ fieldHoles offset active := by
    simp only [fieldHoles, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i _ hi
    apply hne
    rw [eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [f, normal, hi]
  have hy : z true ∈ ys := Finset.mem_image_of_mem Prod.snd hhole
  have hnot : z true ∉ ys := by simpa [S] using (Finset.mem_sdiff.mp (hz true)).2
  exact hnot hy

def B : ℤ := 733296564000
def Q : ℕ := 16865820972000
def lift (w : ℤ × ℤ) (z : F × F) : ℤ × ℤ :=
  (w.1 + B * z.1.val, w.2 + B * z.2.val)
def rowCovers (i : Fin 33) (c : Fin 33 → ℤ) (z : ℤ × ℤ) : Prop :=
  (rows i).e ∣ (rows i).a * z.1 + (rows i).b * z.2 - c i
def lower (i : Fin 33) : ℤ := (rows i).e / 23
def carry (w : ℤ × ℤ) (c : Fin 33 → ℤ) (i : Fin 33) : ℤ :=
  c i - (rows i).a * w.1 - (rows i).b * w.2
def offset (w : ℤ × ℤ) (c : Fin 33 → ℤ) (i : Fin 33) : F :=
  (carry w c i / lower i : ℤ) * ((B / lower i : ℤ) : F)⁻¹

/-- The literal union uses one fixed phase for each original row. -/
def removedRowsCover (c : Fin 33 → ℤ) (z : ℤ × ℤ) : Prop :=
  ∃ i, rowCovers i c z

def pairedCover (c : Fin 33 → ℤ) (z : ℤ × ℤ) : Prop :=
  removedRowsCover c z ∨ removedRowsCover c (z.1 + (Q : ℤ) / 2, z.2)

def residue (z : ℤ × ℤ) : ZMod Q × ZMod Q := (z.1, z.2)

/-- Uncovered lifts are counted as distinct residues modulo Q. -/
def cosetHoles (w : ℤ × ℤ) (c : Fin 33 → ℤ) : Finset (ZMod Q × ZMod Q) := by
  classical
  exact (Finset.univ.filter fun z : F × F => ¬pairedCover c (lift w z)).image
    (fun z => residue (lift w z))

/-- The retained predicate is constant under all integer B-translations. -/
def BPeriodic (U : ℤ × ℤ → Prop) : Prop :=
  ∀ w t : ℤ × ℤ, U (w.1 + B * t.1, w.2 + B * t.2) ↔ U w

/-- A critical coset has fewer than twelve paired holes, or these same fixed
phases repair global failure of a B-periodic retained predicate. -/
def claim : Prop :=
  ∃ (c : Fin 33 → ℤ) (w : ℤ × ℤ), (cosetHoles w c).card < 12 ∨
    ∃ U : ℤ × ℤ → Prop, BPeriodic U ∧
      (∀ z, U z ∨ pairedCover c z) ∧ ¬∀ z, U z

/-- The 33 original rows cannot cover a critical coset or repair global failure
of a retained B-periodic predicate, even with the paired translate. -/
theorem result : ¬claim := by
  classical
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  have facts : ∀ i : Fin 33, lower i ≠ 0 ∧ (rows i).e = lower i * 23 ∧
      lower i ∣ B ∧ ((B / lower i : ℤ) : F) ≠ 0 ∧ (rows i).e ∣ (Q : ℤ) / 2 := by
    intro j
    fin_cases j <;> norm_num [rows, lower, B, Q,
      ZMod.intCast_zmod_eq_zero_iff_dvd] <;> decide +kernel
  -- Integer coordinates include negative and shifted representatives.
  have hcoordinates (w : ℤ × ℤ) (c : Fin 33 → ℤ) (i : Fin 33) (z : ℤ × ℤ) :
      rowCovers i c (w.1 + B * z.1, w.2 + B * z.2) ↔ lower i ∣ carry w c i ∧
        (rows i).a * (z.1 : F) + (rows i).b * (z.2 : F) = offset w c i := by
    obtain ⟨hm, he, hmB, hs, _⟩ := facts i
    let t : ℤ := (rows i).a * z.1 + (rows i).b * z.2
    have hrewrite : (rows i).a * (w.1 + B * z.1) + (rows i).b * (w.2 + B * z.2) - c i =
        B * t - carry w c i := by dsimp [t, carry]; ring
    change (rows i).e ∣ _ ↔ _
    rw [hrewrite]
    by_cases hg : lower i ∣ carry w c i
    · have hfactor : B * t - carry w c i =
          lower i * ((B / lower i) * t - carry w c i / lower i) := by
        rw [mul_sub, ← mul_assoc, Int.mul_ediv_cancel' hmB, Int.mul_ediv_cancel' hg]
      rw [hfactor, he, mul_dvd_mul_iff_left hm, and_iff_right hg]
      have hz := ZMod.intCast_zmod_eq_zero_iff_dvd
        (B / lower i * t - carry w c i / lower i) 23
      norm_num only [Nat.cast_ofNat] at hz
      rw [← hz]
      simp only [Int.cast_sub, Int.cast_mul, sub_eq_zero]
      have ht : (t : F) = (rows i).a * (z.1 : F) + (rows i).b * (z.2 : F) := by
        simp [t]
      rw [ht]
      dsimp [offset]
      rw [eq_mul_inv_iff_mul_eq₀ hs, mul_comm]
    · constructor
      · intro h
        exfalso
        apply hg
        have hmE : lower i ∣ (rows i).e := by rw [he]; exact dvd_mul_right _ _
        have hmd := dvd_sub (dvd_mul_of_dvd_left hmB t) (dvd_trans hmE h)
        simpa using hmd
      · exact fun h => (hg h.1).elim
  have hshift (c : Fin 33 → ℤ) (i : Fin 33) (z : ℤ × ℤ) :
      rowCovers i c (z.1 + (Q : ℤ) / 2, z.2) ↔ rowCovers i c z := by
    apply dvd_iff_dvd_of_dvd_sub
    convert dvd_mul_of_dvd_right (facts i).2.2.2.2 (rows i).a using 1
    ring
  have hpaired (c : Fin 33 → ℤ) (z : ℤ × ℤ) :
      pairedCover c z ↔ removedRowsCover c z := by
    simp only [pairedCover, removedRowsCover, hshift, or_self]
  have hinj (w : ℤ × ℤ) : Function.Injective (fun z : F × F => residue (lift w z)) := by
    intro x y h
    have hc (a b : F) (v : ℤ)
        (he : ((v + B * a.val : ℤ) : ZMod Q) = ((v + B * b.val : ℤ) : ZMod Q)) : a = b := by
      have hz : (((v + B * a.val) - (v + B * b.val) : ℤ) : ZMod Q) = 0 := by
        simpa only [Int.cast_sub, sub_eq_zero] using he
      have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ Q).mp hz
      have heq : (v + B * a.val) - (v + B * b.val) = B * ((a.val : ℤ) - b.val) := by ring
      rw [heq] at hd
      have hQB : (Q : ℤ) = B * 23 := by norm_num [Q, B]
      rw [hQB, mul_dvd_mul_iff_left (by norm_num [B] : B ≠ 0)] at hd
      have hf : (((a.val : ℤ) - b.val : ℤ) : F) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ 23).mpr hd
      simpa [sub_eq_zero] using hf
    apply Prod.ext
    · exact hc _ _ w.1 (congrArg Prod.fst h)
    · exact hc _ _ w.2 (congrArg Prod.snd h)
  have hholes (w : ℤ × ℤ) (c : Fin 33 → ℤ) : 12 ≤ (cosetHoles w c).card := by
    let active := Finset.univ.filter fun i => lower i ∣ carry w c i
    have heq : (Finset.univ.filter fun z : F × F => ¬pairedCover c (lift w z)) =
        fieldHoles (offset w c) active := by
      ext z
      have hpull (i : Fin 33) := hcoordinates w c i
        ((z.1.val : ℤ), (z.2.val : ℤ))
      simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at hpull
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, fieldHoles, hpaired,
        removedRowsCover, not_exists, lift, hpull, not_and, active]
    unfold cosetHoles
    rw [Finset.card_image_of_injective _ (hinj w), heq]
    exact affine_holes _ _
  rintro ⟨c, w, hsmall | ⟨U, hU, hall, hfail⟩⟩
  · exact (not_lt_of_ge (hholes w c)) hsmall
  · apply hfail
    intro v
    have hn : (cosetHoles v c).Nonempty := Finset.card_pos.mp (by have := hholes v c; omega)
    obtain ⟨_, hp⟩ := hn
    change _ ∈ (Finset.univ.filter fun z : F × F => ¬pairedCover c (lift v z)).image
      (fun z => residue (lift v z)) at hp
    obtain ⟨z, hz, _⟩ := Finset.mem_image.mp hp
    have hz' : ¬pairedCover c (lift v z) := (Finset.mem_filter.mp hz).2
    have hu : U (lift v z) := (hall (lift v z)).resolve_right hz'
    exact (hU v (z.1.val, z.2.val)).mp hu

end

end D5.S3.Arith.Covering.CriticalCosetObstruction

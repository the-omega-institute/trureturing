/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/FiniteGapCircuit
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The twelve finite-degree entries as polynomial circuits in two reciprocal gaps. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.FiniteGapPolynomial
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.PackedPolynomialSign
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineSignPolynomials

/-! Evaluate the finite-degree reciprocal-gap polynomials directly at the radix. -/

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum

open FourCopyGap
open RefinedBMV.DividedDifference.SparseExpansion
open private BoundedExpansion BoundedExpansion.single BoundedExpansion.eval
  BoundedExpansion.degree BoundedExpansion.mass BoundedExpansion.mass_nonneg
  eval_bounded_add eval_bounded_sub eval_bounded_mul eval_bounded_pow eval_bounded_nat
  eval_bounded_single from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumBinding

private def gapList (p : ℕ) : List Gap :=
  let r := List.range (p + 1)
  (r ×ˢ (r ×ˢ (r ×ˢ r))).filter
    (fun g => g.1 + g.2.1 + g.2.2.1 + g.2.2.2 == p)

private theorem gapList_nodup (p : ℕ) : (gapList p).Nodup := by
  unfold gapList
  exact (List.nodup_range.product
    (List.nodup_range.product (List.nodup_range.product List.nodup_range))).filter _

private theorem gapList_toFinset (p : ℕ) : (gapList p).toFinset = gaps p := by
  ext g
  obtain ⟨a, b, c, d⟩ := g
  simp only [List.mem_toFinset, gapList, List.mem_filter, List.mem_product, List.mem_range,
    beq_iff_eq, mem_gaps]
  omega

private def gapWord {R : Type*} [Mul R] [Pow R ℕ] (a b c d : R) (g : Gap) : R :=
  (a ^ 4) ^ g.1 * (b ^ 4) ^ g.2.1 * (c ^ 4) ^ g.2.2.1 * (d ^ 4) ^ g.2.2.2

private def gapCircuit {R : Type*} [Add R] [Sub R] [Mul R] [Pow R ℕ] [OfNat R 0]
    (cast : ℕ → R) (p : ℕ) (a b c d : R) : R :=
  let gs := gapList p
  gs.foldr (fun g acc => gapWord a b c d g + acc) 0 - cast gs.length * (a * b * c * d) ^ p

private theorem foldr_add_eq {R : Type*} [AddMonoid R] {T : Type*} (l : List T) (f : T → R) :
    l.foldr (fun g acc => f g + acc) 0 = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons head tail ih => simp [ih]

private theorem gapCircuit_eq {R : Type*} [CommRing R] (p : ℕ) (a b c d : R) :
    gapCircuit (fun n : ℕ => (n : R)) p a b c d = finiteGapPolynomial p a b c d := by
  rw [gapCircuit, foldr_add_eq, ← List.sum_toFinset _ (gapList_nodup p),
    ← List.toFinset_card_of_nodup (gapList_nodup p), gapList_toFinset]
  rfl

private def constant (n : ℕ) : BoundedExpansion :=
  BoundedExpansion.single ⟨0, 0, 0, 0, 0⟩ n

private theorem eval_foldr_gap {R : Type*} [CommRing R] (p x y u v : R)
    (a b c d : BoundedExpansion) (gs : List Gap) :
    BoundedExpansion.eval p x y u v (gs.foldr (fun g acc => gapWord a b c d g + acc) 0) =
      gs.foldr (fun g acc => gapWord (BoundedExpansion.eval p x y u v a)
        (BoundedExpansion.eval p x y u v b) (BoundedExpansion.eval p x y u v c)
        (BoundedExpansion.eval p x y u v d) g + acc) 0 := by
  induction gs with
  | nil => simpa using eval_bounded_nat p x y u v 0
  | cons g gs ih =>
    simp only [List.foldr_cons, eval_bounded_add]
    rw [ih]
    simp only [gapWord, eval_bounded_mul, eval_bounded_pow]

private theorem eval_gapCircuit {R : Type*} [CommRing R] (p : ℕ) (x y z u v : R)
    (a b c d : BoundedExpansion) :
    BoundedExpansion.eval x y z u v (gapCircuit constant p a b c d) =
      finiteGapPolynomial p (BoundedExpansion.eval x y z u v a)
        (BoundedExpansion.eval x y z u v b) (BoundedExpansion.eval x y z u v c)
        (BoundedExpansion.eval x y z u v d) := by
  rw [← gapCircuit_eq]
  simp [gapCircuit, constant, eval_foldr_gap, eval_bounded_sub, eval_bounded_mul,
    eval_bounded_pow, eval_bounded_single]

private def firstGap : BoundedExpansion := BoundedExpansion.single ⟨1, 0, 0, 0, 0⟩ 1
private def secondGap : BoundedExpansion := BoundedExpansion.single ⟨0, 1, 0, 0, 0⟩ 1

def reciprocalEntryCircuit (p : ℕ) (j : Fin 12) : BoundedExpansion :=
  let a : BoundedExpansion := 1
  let b := 1 + firstGap
  let c := b * (1 + secondGap)
  let D := gapCircuit constant p
  (![D a a a b, D a a a c, D b b b a, D b b b c, D c c c a, D c c c b,
    D a a b c, D b b a c, D c c a b, D a a b b, D a a c c, D b b c c] : Fin 12 → BoundedExpansion) j

theorem eval_reciprocalEntryCircuit {R : Type*} [CommRing R] (p : ℕ) (x y z u v : R)
    (j : Fin 12) :
    BoundedExpansion.eval x y z u v (reciprocalEntryCircuit p j) =
      finiteSpectralEntries p 1 (1 + x) ((1 + x) * (1 + y)) j := by
  fin_cases j <;>
    simp [reciprocalEntryCircuit, finiteSpectralEntries, eval_gapCircuit, firstGap, secondGap,
      eval_bounded_add, eval_bounded_mul, eval_bounded_nat x y z u v 1, eval_bounded_single]

private def finiteSignCircuit (p : ℕ) (sign : GramSign) : BoundedExpansion :=
  sign.value (reciprocalEntryCircuit p)

private theorem eval_finiteSignCircuit {R : Type*} [CommRing R]
    (p : ℕ) (sign : GramSign) (x y z u v : R) :
    BoundedExpansion.eval x y z u v (finiteSignCircuit p sign) =
      sign.value (finiteSpectralEntries p 1 (1 + x) ((1 + x) * (1 + y))) := by
  cases sign <;>
    simp [finiteSignCircuit, GramSign.value, QuarticData.ofGapEntries,
      QuarticData.axis1, QuarticData.axis2, QuarticData.axis3,
      QuarticData.mixed1, QuarticData.mixed2, QuarticData.mixed3,
      QuarticData.alpha, QuarticData.beta, QuarticData.gamma,
      QuarticData.RX, QuarticData.RY, QuarticData.RZ, QuarticData.J,
      QuarticData.KX, QuarticData.KY, QuarticData.KZ,
      QuarticData.delta1, QuarticData.delta2, QuarticData.delta3, eval_reciprocalEntryCircuit,
      eval_bounded_add, eval_bounded_sub, eval_bounded_mul, eval_bounded_pow,
      eval_bounded_nat x y z u v 2, eval_bounded_nat x y z u v 4]

open AffineRadixIdentity

private def digitSizes (a : BoundedExpansion) : Exponents :=
  let d := BoundedExpansion.degree a
  ⟨d.p + 1, d.x + 1, d.y + 1, d.u + 1, d.v + 1⟩

private def digitWidth (a : BoundedExpansion) : ℕ :=
  (BoundedExpansion.mass a).toNat.log2 + 1

def checkFiniteSign (p : ℕ) (sign : GramSign) : Bool :=
  let a := finiteSignCircuit p sign
  let sizes := digitSizes a
  let w := digitWidth a
  let b := radix w
  passesSignMask w (index sizes (BoundedExpansion.degree a) + 1)
    (sign.value (finiteSpectralEntries p 1 (1 + b) ((1 + b) * (1 + b ^ sizes.p))))

private theorem nonneg_finiteSign_of_check (p : ℕ) (sign : GramSign)
    (h : checkFiniteSign p sign = true) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ sign.value (finiteSpectralEntries p 1 (1 + x) ((1 + x) * (1 + y))) := by
  let a := finiteSignCircuit p sign
  let sizes := digitSizes a
  let w := digitWidth a
  let digits := index sizes (BoundedExpansion.degree a) + 1
  have hfit : Fits sizes (BoundedExpansion.degree a) := by
    unfold sizes digitSizes Fits
    exact ⟨Nat.lt_succ_self _, Nat.lt_succ_self _, Nat.lt_succ_self _, Nat.lt_succ_self _,
      Nat.lt_succ_self _⟩
  have hmass : BoundedExpansion.mass a < (2 : ℤ) ^ w := by
    have hb : (BoundedExpansion.mass a).toNat < 2 ^ w := Nat.lt_log2_self
    have hb' : ((BoundedExpansion.mass a).toNat : ℤ) < (2 : ℤ) ^ w := by exact_mod_cast hb
    simpa only [Int.toNat_of_nonneg (BoundedExpansion.mass_nonneg a)] using hb'
  have hn := boundedExpansion_nonneg_of_mask sizes w digits a hfit
    (Nat.succ_pos _) (Nat.lt_succ_self _) hmass
    (by
      dsimp only
      rw [show a = finiteSignCircuit p sign by rfl, eval_finiteSignCircuit]
      exact h)
    x y 1 1 1 hx hy zero_le_one zero_le_one zero_le_one
  simpa only [a, eval_finiteSignCircuit] using hn

theorem finiteSigns_of_checks (p : ℕ) (h : ∀ sign, checkFiniteSign p sign = true)
    {r t : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1) :
    (kernelQuarticData (fun i j k l ↦
      2 * spectralDefect p ![r^4*t^4, t^4, 1] i j k l)).SixSigns := by
  apply sixSigns_of_reciprocalEntries p hr ht
  apply sixSigns_of_gramSigns
  intro sign
  have hx : 0 ≤ r⁻¹ - 1 := sub_nonneg.mpr ((one_le_inv₀ hr).mpr hr1)
  have hy : 0 ≤ t⁻¹ - 1 := sub_nonneg.mpr ((one_le_inv₀ ht).mpr ht1)
  have h₁ : 1 + (r⁻¹ - 1) = r⁻¹ := by ring
  have h₂ : 1 + (t⁻¹ - 1) = t⁻¹ := by ring
  simpa only [h₁, h₂] using nonneg_finiteSign_of_check p sign (h sign) hx hy

end RefinedBMV.ThreeBlockGram.PositiveSpectrum

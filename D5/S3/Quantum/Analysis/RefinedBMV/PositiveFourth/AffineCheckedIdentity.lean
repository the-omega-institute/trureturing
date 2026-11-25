/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/AffineCheckedIdentity
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Check the polynomial identity between a grouped quotient and its Gram sign. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineCertificateBounds
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineCircuit
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineTablePacking

/-! Structural degree and mass bounds choose an injective packed evaluation.
The concrete check computes with the factored expressions and grouped table. -/

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.AffineRadixIdentity

open RefinedBMV.DividedDifference.SparseExpansion
open GroupedAffineMasks (Certificate Group)
open private termExponents coefficientTerms from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineTableTerms
open private sum_map_flatMap from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.GroupedAffineMasks
open private BoundedExpansion BoundedExpansion.degree BoundedExpansion.mass
  Exponents.bounded Exponents.plus Exponents.sup coeffMass
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumBinding

private def paddedSizes (a b : Exponents) : Exponents :=
  let d := Exponents.sup a b
  ⟨d.p + 1, d.x + 1, d.y + 1, d.u + 1, d.v + 1⟩

private theorem fits_padded_left (a b : Exponents) : Fits (paddedSizes a b) a := by
  simp only [Fits, paddedSizes, Exponents.sup, Nat.lt_succ_iff]
  exact ⟨Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _,
    Nat.le_max_left _ _, Nat.le_max_left _ _⟩

private theorem fits_padded_right (a b : Exponents) : Fits (paddedSizes a b) b := by
  simp only [Fits, paddedSizes, Exponents.sup, Nat.lt_succ_iff]
  exact ⟨Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _,
    Nat.le_max_right _ _, Nat.le_max_right _ _⟩

private def boundedGroup (start : ℕ) (degree : Exponents)
    (v : AffineRate) (g : Group) : Bool :=
  decide (g.coefficients.length ≤ degree.p + 1 ∧
    Exponents.bounded (termExponents start g.rateU v 0) degree)

private def boundedTable (c : Certificate) (start : ℕ) (degree : Exponents) : Bool :=
  c.columns.all fun (v, groups) => groups.all (boundedGroup start degree v)

private theorem coefficientTerms_bounded (start : ℕ) (degree : Exponents) (u v : AffineRate)
    (hbase : Exponents.bounded (termExponents start u v 0) degree)
    (cs : List ℤ) (d : ℕ) (hlen : d + cs.length ≤ degree.p + 1)
    (t : Term) (ht : t ∈ coefficientTerms start u v d cs) :
    Exponents.bounded t.exponents degree := by
  induction cs generalizing d with
  | nil => simp [coefficientTerms] at ht
  | cons a cs ih =>
    simp only [coefficientTerms, List.mem_cons] at ht
    simp only [List.length_cons] at hlen
    rcases ht with rfl | ht
    · exact ⟨by change d ≤ degree.p; omega, hbase.2⟩
    · exact ih (d + 1) (by omega) ht

private theorem tableTerms_bounded (c : Certificate) (start : ℕ) (degree : Exponents)
    (h : boundedTable c start degree = true) (t : Term) (ht : t ∈ c.tableTerms start) :
    Exponents.bounded t.exponents degree := by
  simp only [boundedTable, List.all_eq_true, boundedGroup, decide_eq_true_eq] at h
  simp only [Certificate.tableTerms, Certificate.terms, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨⟨v, g⟩, ⟨col, hcol, g', hg, heq⟩, hterm⟩ := ht
  cases heq
  have hgroup := h col hcol _ hg
  exact coefficientTerms_bounded start degree _ _ hgroup.2 _ 0
    (by simpa only [zero_add] using hgroup.1) t hterm

private def tableMass (c : Certificate) : ℤ :=
  (c.columns.map fun col =>
    (col.2.map fun g => GroupedAffineMasks.coefficientMass g.coefficients).sum).sum

private theorem coefficientTerms_mass (start : ℕ) (u v : AffineRate) (d : ℕ)
    (cs : List ℤ) :
    coefficientMass (coefficientTerms start u v d cs) = GroupedAffineMasks.coefficientMass cs := by
  induction cs generalizing d with
  | nil => rfl
  | cons a cs ih =>
    simp only [coefficientTerms, coeffMass, GroupedAffineMasks.coefficientMass, List.map_cons,
      List.sum_cons]
    simpa only [coeffMass, GroupedAffineMasks.coefficientMass] using
      congrArg (fun n : ℤ => |a| + n) (ih (d + 1))

private theorem tableMass_eq (c : Certificate) (start : ℕ) :
    tableMass c = coefficientMass (c.tableTerms start) := by
  simp only [tableMass, Certificate.tableTerms, Certificate.terms, coeffMass, sum_map_flatMap,
    List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨v, groups⟩ _
  apply congrArg List.sum
  apply List.map_congr_left
  intro g _
  exact (coefficientTerms_mass start g.rateU v 0 g.coefficients).symm

private def identitySizes (sign : GramSign) (degree : Exponents) : Exponents :=
  paddedSizes (Exponents.plus (BoundedExpansion.degree (factorExpansion sign)) degree)
    (BoundedExpansion.degree (signExpansion sign))

private def identityMass (sign : GramSign) (tableMass : ℤ) : ℤ :=
  BoundedExpansion.mass (factorExpansion sign) * tableMass +
    BoundedExpansion.mass (signExpansion sign)

private def identityWidth (sign : GramSign) (tableMass : ℤ) : ℕ :=
  (identityMass sign tableMass).toNat.log2 + 1

def checkIdentity (sign : GramSign) (c : Certificate) (start : ℕ) (degree : Exponents) : Bool :=
  let sizes := identitySizes sign degree
  let bits := identityWidth sign (tableMass c) + 1
  let b := (1 : ℤ) <<< bits
  let r := (1 : ℤ) <<< (bits * sizes.p)
  let t := (1 : ℤ) <<< (bits * (sizes.p * sizes.x))
  let u := (1 : ℤ) <<< (bits * (sizes.p * sizes.x * sizes.y))
  let v := (1 : ℤ) <<< (bits * (sizes.p * sizes.x * sizes.y * sizes.u))
  boundedTable c start degree && decide
    (sign.removedFactor b r t u v * c.groupedPackedEval start sizes bits =
      sign.value (affineEntries b r t u v))

theorem factor_mul_table_of_checkIdentity {R : Type*} [CommRing R]
    (sign : GramSign) (c : Certificate) (start : ℕ) (degree : Exponents)
    (h : checkIdentity sign c start degree = true) (x r t u v : R) :
    sign.removedFactor x r t u v * evalTerms x r t u v (c.tableTerms start) =
      sign.value (affineEntries x r t u v) := by
  simp only [checkIdentity, Bool.and_eq_true, decide_eq_true_eq,
    c.groupedPackedEval_eq, Int.shiftLeft_eq, one_mul, pow_mul] at h
  have hb := tableTerms_bounded c start degree h.1
  let terms := c.tableTerms start
  let width := identityWidth sign (tableMass c)
  have hm : identityMass sign (coefficientMass terms) < (2 : ℤ) ^ width := by
    rw [show coefficientMass terms = tableMass c from (tableMass_eq c start).symm]
    have hn : (identityMass sign (tableMass c)).toNat < 2 ^ width := Nat.lt_log2_self
    exact (Int.self_le_toNat _).trans_lt (by exact_mod_cast hn)
  exact factor_mul_evalTerms_eq_signValue sign terms degree (identitySizes sign degree) width
    hb (fits_padded_left _ _) (fits_padded_right _ _) hm
    (by simpa only [width, terms, radix, pow_mul] using h.2) x r t u v

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.AffineRadixIdentity

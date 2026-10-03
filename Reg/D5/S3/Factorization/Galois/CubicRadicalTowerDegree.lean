import D5.S3.Factorization.Galois.CubicRadicalTowerDegree
import Reg.Support.DependentFamily
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Factorization.Galois.CubicRadicalTowerDegree
open LeanInformationAudit
open scoped WithZero

namespace Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => 3 ^ n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

-- Only the source's degree target is observed. Every field, finite index family,
-- root equation, valuation matrix, and unit hypothesis stays in the law.
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {K L : Type} [Field K] [Field L] [Algebra K L]
    {ι : Type} [Fintype ι]
    (ζ : K) (hζ : IsPrimitiveRoot ζ 3)
    (rad : ι → K) (root : ι → L)
    (hroot : ∀ i, root i ^ 3 = algebraMap K L (rad i))
    (hrad : ∀ i, rad i ≠ 0)
    (ν : ι → Valuation K (WithZero (Multiplicative ℤ)))
    (hdiag : ∀ i, ¬ (3 : ℤ) ∣ WithZero.log (ν i (rad i)))
    (hoff : ∀ i j, i ≠ j → ν i (rad j) = 1)
    (u : K) (hu0 : u ≠ 0) (hunoncube : ¬ ∃ c : K, c ^ 3 = u)
    (huval : ∀ i, WithZero.log (ν i u) = 0),
    Module.finrank K (IntermediateField.adjoin K (Set.range root)) =
        R.readout () () (Fintype.card ι) ∧
      ∀ x : IntermediateField.adjoin K (Set.range root),
        x ^ 3 ≠ algebraMap K (IntermediateField.adjoin K (Set.range root)) u

private theorem cyclotomic_unit_noncube :
    let K := CyclotomicField 3 ℚ
    letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
    letI : IsCyclotomicExtension {3} ℚ K :=
      CyclotomicField.isCyclotomicExtension 3 ℚ
    ¬ ∃ x : K, x ^ 3 = IsCyclotomicExtension.zeta 3 ℚ K := by
  dsimp only
  let K := CyclotomicField 3 ℚ
  letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {3} ℚ K :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  let ζ : K := IsCyclotomicExtension.zeta 3 ℚ K
  have hζ : IsPrimitiveRoot ζ 3 := IsCyclotomicExtension.zeta_spec 3 ℚ K
  rintro ⟨x, hx⟩
  have hnot : x ^ 3 ≠ 1 := by
    rw [hx]
    exact hζ.ne_one (by decide)
  have h9 : x ^ 9 = 1 := by
    calc
      x ^ 9 = (x ^ 3) ^ 3 := by ring
      _ = ζ ^ 3 := by rw [hx]
      _ = 1 := hζ.pow_eq_one
  have horder : orderOf x = 9 := by
    have h := orderOf_eq_prime_pow (p := 3) (n := 1)
      (by simpa only [pow_one] using hnot)
      (by simpa only [show (3 : ℕ) ^ (1 + 1) = 9 by decide] using h9)
    norm_num at h
    exact h
  have hroot9 : IsPrimitiveRoot x 9 := IsPrimitiveRoot.iff_orderOf.mpr horder
  have hdiv : 9 ∣ 2 * 3 := hroot9.dvd_of_isCyclotomicExtension 3 (by decide)
  norm_num at hdiv

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let K := CyclotomicField 3 ℚ
  letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {3} ℚ K :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  let ζ : K := IsCyclotomicExtension.zeta 3 ℚ K
  have hζ : IsPrimitiveRoot ζ 3 := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have hζ0 : ζ ≠ 0 := by
    intro hz
    have hp := hζ.pow_eq_one
    rw [hz] at hp
    norm_num at hp
  have hnc : ¬ ∃ x : K, x ^ 3 = ζ := cyclotomic_unit_noncube
  have hdegree := (h (K := K) (L := K) (ι := Empty)
    ζ hζ (fun i => nomatch i) (fun i => nomatch i)
    (by intro i; exact nomatch i)
    (by intro i; exact nomatch i)
    (fun i => nomatch i)
    (by intro i; exact nomatch i)
    (by intro i; exact nomatch i)
    ζ hζ0 hnc (by intro i; exact nomatch i)).1
  have hrange : Set.range (fun i : Empty => (nomatch i : K)) = ∅ := by
    ext x
    simp
  rw [hrange, IntermediateField.adjoin_empty] at hdegree
  simpa [rejected, realize] using hdegree

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    intro K L _ _ _ ι _ ζ hζ rad root hroot hrad ν hdiag hoff u hu0 hunoncube huval
    exact finite_valuation_degree_and_unit_noncube
      ζ hζ rad root hroot hrad ν hdiag hoff u hu0 hunoncube huval
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (3 : ℕ) ^ 0 ≠ 3 ^ 1
    norm_num

register_information_theorem
  _root_.D5.S3.Factorization.Galois.CubicRadicalTowerDegree.finite_valuation_degree_and_unit_noncube
  in arena
  readout via (realize signature (fun _ _ n => 3 ^ n) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Factorization.Galois.CubicRadicalTowerDegree
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      stateOperand := some #["arg"]}] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S3.Factorization.Galois.CubicRadicalTowerDegree

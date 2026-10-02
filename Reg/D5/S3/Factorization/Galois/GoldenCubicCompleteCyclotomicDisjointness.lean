import D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness
import Reg.Support.DependentFamily
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness
open _root_.D5.S1.Scale
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open _root_.D5.S3.Factorization.QuadraticIdeals.GoldenCubicPrimaryProduct
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinCyclotomicBridge
open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open _root_.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods
open LeanInformationAudit NumberField IsDedekindDomain
open scoped WithZero

namespace Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness

noncomputable section

local instance : IsCyclotomicExtension {3} ℚ E :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

abbrev signature : Signature where
  Params := Unit
  State := fun _ => L
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => IntermediateField E L
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ζ => actualCyclotomic ζ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (⊤ : IntermediateField E L)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (j : ℕ),
    let φ : EisensteinOrder ≃ₐ[ℤ] 𝓞 E := Classical.choice eisenstein_cyclotomic_equiv_exists
    let B : ℕ → ℕ := blockValue
    let S : Finset ℕ := support j
    let I := radicalIndex j
    ∃ ζ : L, IsPrimitiveRoot ζ (modulus j) ∧
      ∃ π : ℕ → EisensteinOrder, ∃ root : I → L,
        ((∀ p ∈ S,
          (Ideal.span {π p}).IsPrime ∧ QuadraticAlgebra.norm (π p) = (p : ℤ) ∧
          (3 : EisensteinOrder) ∣ π p - 1 ∧ p % 3 = 1 ∧
          IsCoprime (π p) (star (π p))) ∧
        (∀ p ∈ S, ∀ q ∈ S, p ≠ q →
          IsCoprime (π p) (π q) ∧ IsCoprime (π p) (star (π q)) ∧
          IsCoprime (star (π p)) (π q) ∧ IsCoprime (star (π p)) (star (π q))) ∧
        (∀ i, 1 ≤ i → i < j →
          orientedFactor ((goldenLucas (3 ^ i) - 1).toNat) =
            ∏ p ∈ (B i).primeFactors,
              π p ^ padicValNat p (Nat.fib (fibonacciRank p))) ∧
        (∀ v : I, root v ^ 3 = algebraMap E L
          ((Sum.elim (fun w => φ (if w.2 then star (π w.1.val) else π w.1.val))
            (fun k => if k.val = 0 then (2 : 𝓞 E) else 3) v) : E)) ∧
        Module.finrank E (IntermediateField.adjoin E (Set.range root)) =
          3 ^ (2 * S.card + 2) ∧
        (∀ x : IntermediateField.adjoin E (Set.range root),
          x ^ 3 ≠ algebraMap E (IntermediateField.adjoin E (Set.range root))
            (IsCyclotomicExtension.zeta 3 ℚ E)) ∧
        IsGalois E (IntermediateField.adjoin E (Set.range root)) ∧
        (∃ e : ((IntermediateField.adjoin E (Set.range root)) ≃ₐ[E]
            (IntermediateField.adjoin E (Set.range root))) ≃*
            (I → Multiplicative (ZMod 3)),
          ∀ σ : (IntermediateField.adjoin E (Set.range root)) ≃ₐ[E]
              (IntermediateField.adjoin E (Set.range root)), ∀ i : I,
            σ (⟨root i, IntermediateField.subset_adjoin E (Set.range root) ⟨i, rfl⟩⟩ :
                IntermediateField.adjoin E (Set.range root)) =
              algebraMap E (IntermediateField.adjoin E (Set.range root))
                (IsCyclotomicExtension.zeta 3 ℚ E) ^
                (Multiplicative.toAdd (e σ i)).val *
                  (⟨root i, IntermediateField.subset_adjoin E (Set.range root) ⟨i, rfl⟩⟩ :
                    IntermediateField.adjoin E (Set.range root)))) ∧
        IntermediateField.adjoin E (Set.range root) ⊓ R.readout () () ζ = ⊥

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h 0
  dsimp only at hzero
  obtain ⟨ζ, hζ, π, root, hdata, hmeet⟩ := hzero
  let M : IntermediateField E L := IntermediateField.adjoin E (Set.range root)
  have hdegree : Module.finrank E M = 3 ^ (2 * (support 0).card + 2) :=
    hdata.2.2.2.2.1
  have hMbot : M = ⊥ := by
    change M ⊓ ⊤ = ⊥ at hmeet
    simpa only [inf_top_eq] using hmeet
  rw [hMbot, IntermediateField.finrank_bot] at hdegree
  norm_num [support] at hdegree

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    exact actual_complete_cubic_cyclotomic_disjointness
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
    letI : NeZero (modulus 0 : E) := ⟨by norm_num [modulus]⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (modulus 0)
    refine ⟨(), (0 : L), ζ, ?_⟩
    intro heq
    change actualCyclotomic (0 : L) = actualCyclotomic ζ at heq
    have hzero : actualCyclotomic (0 : L) = ⊥ := by
      change IntermediateField.adjoin E {(0 : L)} = ⊥
      apply IntermediateField.adjoin_eq_bot_iff.mpr
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact (⊥ : IntermediateField E L).zero_mem
    have hζbot : actualCyclotomic ζ = ⊥ := heq.symm.trans hzero
    have hζmem : ζ ∈ (⊥ : IntermediateField E L) := by
      rw [← hζbot]
      exact IntermediateField.mem_adjoin_simple_self E ζ
    obtain ⟨x, hx⟩ := IntermediateField.mem_bot.mp hζmem
    have hxprim : IsPrimitiveRoot x (modulus 0) := by
      have hmapped : IsPrimitiveRoot (algebraMap E L x) (modulus 0) := by
        simpa only [hx] using hζ
      exact hmapped.of_map_of_injective (algebraMap E L).injective
    have hdiv : modulus 0 ∣ 2 * 3 :=
      hxprim.dvd_of_isCyclotomicExtension 3 (by norm_num [modulus])
    norm_num [modulus] at hdiv

register_information_theorem
  _root_.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness.actual_complete_cubic_cyclotomic_disjointness
  in arena
  readout via (realize signature (fun _ _ ζ => actualCyclotomic ζ)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body",
        "arg", "arg", "body", "arg", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 5 }] })
  escape continues (open)

#print axioms registration

end
end Reg.D5.S3.Factorization.Galois.GoldenCubicCompleteCyclotomicDisjointness

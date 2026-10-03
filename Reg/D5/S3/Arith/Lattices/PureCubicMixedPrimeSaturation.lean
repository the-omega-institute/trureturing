import D5.S3.Arith.Lattices.PureCubicMixedPrimeSaturation
import Reg.Support.DependentFamily
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.Field.ULift

open _root_.D5.S3.Arith.Lattices.PureCubicMixedPrimeSaturation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial Module

namespace Reg.D5.S3.Arith.Lattices.PureCubicMixedPrimeSaturation
universe u

noncomputable section

abbrev signature : Signature where
  Params := ℤ
  State := fun _ => ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ m n => m * n ^ 2) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ m n => 2 * m * n ^ 2) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {K : Type u} [Field K] [CharZero K] [Algebra ℚ K]
    (pb : PowerBasis ℚ K) (h3 : pb.dim = 3)
    (m n c a k v : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hv : v = 1 ∨ v = -1)
    (hroot : pb.gen ^ 3 = ((R.readout () m n : ℤ) : K))
    (hcubic : c ^ 3 * m * n ^ 2 = 1 + 9 * a)
    (hcv : c ^ 2 * n = v + 3 * k)
    (p : ℕ) (hp : p.Prime)
    (hlocal :
      ((p : ℤ) ∣ m * n ^ 2 ∧ ¬(p : ℤ) ^ 2 ∣ m * n ^ 2 ∧
        IsCoprime (p : ℤ) (3 * n)) ∨
      ((p : ℤ) ∣ m ^ 2 * n ∧ ¬(p : ℤ) ^ 2 ∣ m ^ 2 * n ∧
        IsCoprime (p : ℤ) (3 * m)))
    (z : K) (hzint : IsIntegral ℤ z)
    (hpz : ∃ u r s : ℤ,
      (p : K) * z = (u : K) + (r : K) * pb.gen +
        (s : K) * ((1 + (c : K) * pb.gen +
          (v : K) * (pb.gen ^ 2 / (n : K))) / 3)),
    ∃ u r s : ℤ,
      z = (u : K) + (r : K) * pb.gen +
        (s : K) * ((1 + (c : K) * pb.gen +
          (v : K) * (pb.gen ^ 2 / (n : K))) / 3)

private theorem twenty_irreducible :
    Irreducible ((X : Polynomial ℚ) ^ 3 - C 20) := by
  have hnocubeInt (z : ℤ) : z ^ 3 ≠ 20 := by
    intro hz
    have hz9 : (z : ZMod 9) ^ 3 = (20 : ZMod 9) := by
      simpa only [Int.cast_pow, Int.cast_ofNat] using
        congrArg (fun x : ℤ => (x : ZMod 9)) hz
    have hnone (w : ZMod 9) : w ^ 3 ≠ (20 : ZMod 9) := by
      fin_cases w <;> decide
    exact hnone (z : ZMod 9) hz9
  have hnocubeRat (r : ℚ) : r ^ 3 ≠ 20 := by
    intro hr
    have hInt : IsIntegral ℤ r := by
      apply IsIntegral.of_pow (n := 3) (by norm_num)
      rw [hr]
      exact isIntegral_algebraMap
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hInt
    apply hnocubeInt z
    rw [← hz] at hr
    apply (Int.cast_injective (α := ℚ))
    simpa only [algebraMap_int_eq, eq_intCast,
      Int.cast_pow, Int.cast_ofNat] using hr
  exact X_pow_sub_C_irreducible_of_prime (by norm_num : Nat.Prime 3) hnocubeRat

private noncomputable def twentyPowerBasis
    [Fact (Irreducible ((X : Polynomial ℚ) ^ 3 - C 20))] :
    PowerBasis ℚ (AdjoinRoot ((X : Polynomial ℚ) ^ 3 - C 20)) :=
  AdjoinRoot.powerBasis (monic_X_pow_sub_C 20 (by norm_num : 3 ≠ 0)).ne_zero

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  letI : Fact (Irreducible ((X : Polynomial ℚ) ^ 3 - C 20)) :=
    ⟨twenty_irreducible⟩
  let K0 := AdjoinRoot ((X : Polynomial ℚ) ^ 3 - C 20)
  let K := ULift.{u} K0
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  let pb : PowerBasis ℚ K :=
    twentyPowerBasis.map (ULift.algEquiv (R := ℚ)).symm
  have h3 : pb.dim = 3 := by
    change (twentyPowerBasis).dim = 3
    simp [twentyPowerBasis]
  have hroot0 : (twentyPowerBasis).gen ^ 3 = (20 : K0) := by
    simpa [twentyPowerBasis, K0] using root_X_pow_sub_C_pow 3 (20 : ℚ)
  have hroot20 : pb.gen ^ 3 = (20 : K) := by
    apply (ULift.algEquiv (R := ℚ)).injective
    change (twentyPowerBasis.gen : K0) ^ 3 = 20
    exact hroot0
  have hroot : pb.gen ^ 3 = ((rejected.readout () 10 1 : ℤ) : K) := by
    change pb.gen ^ 3 = ((20 : ℤ) : K)
    norm_num only [Int.cast_ofNat]
    exact hroot20
  have hcubic : (1 : ℤ) ^ 3 * 10 * 1 ^ 2 = 1 + 9 * 1 := by norm_num
  have hcv : (1 : ℤ) ^ 2 * 1 = 1 + 3 * 0 := by norm_num
  have hv : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  have hm : (10 : ℤ) ≠ 0 := by norm_num
  have hn : (1 : ℤ) ≠ 0 := by norm_num
  have hp : Nat.Prime 2 := Nat.prime_two
  have hlocal :
      ((2 : ℤ) ∣ 10 * 1 ^ 2 ∧ ¬(2 : ℤ) ^ 2 ∣ 10 * 1 ^ 2 ∧
        IsCoprime (2 : ℤ) (3 * 1)) ∨
      ((2 : ℤ) ∣ 10 ^ 2 * 1 ∧ ¬(2 : ℤ) ^ 2 ∣ 10 ^ 2 * 1 ∧
        IsCoprime (2 : ℤ) (3 * 10)) := by
    left
    refine ⟨by norm_num, by norm_num, ?_⟩
    exact ⟨-1, 1, by norm_num⟩
  let z : K := pb.gen ^ 2 / 2
  have hzcube : z ^ 3 = (50 : K) := by
    calc
      z ^ 3 = (pb.gen ^ 3) ^ 2 / (2 : K) ^ 3 := by dsimp [z]; ring
      _ = 50 := by rw [hroot20]; norm_num
  have hzint : IsIntegral ℤ z := by
    apply IsIntegral.of_pow (n := 3) (by norm_num)
    rw [hzcube]
    exact isIntegral_algebraMap
  have hpz : ∃ u r s : ℤ,
      (2 : K) * z = (u : K) + (r : K) * pb.gen +
        (s : K) * ((1 + (1 : K) * pb.gen +
          (1 : K) * (pb.gen ^ 2 / (1 : K))) / 3) := by
    refine ⟨-1, -1, 3, ?_⟩
    dsimp [z]
    norm_num
    ring
  let b : Basis (Fin 3) ℚ K := pb.basis.reindex (finCongr h3)
  have hb (i : Fin 3) : b i = pb.gen ^ (i : ℕ) := by
    simp [b, Basis.reindex_apply, pb.basis_eq_pow]
  have hcoord0 : b.coord 2 (1 : K) = 0 := by
    rw [← show b 0 = (1 : K) by simpa using hb 0]
    simp [Basis.coord_apply]
  have hcoord1 : b.coord 2 pb.gen = 0 := by
    rw [← show b 1 = pb.gen by simpa using hb 1]
    simp [Basis.coord_apply]
  have hcoord2 : b.coord 2 (pb.gen ^ 2) = 1 := by
    rw [← show b 2 = pb.gen ^ 2 by simpa using hb 2]
    simp [Basis.coord_apply]
  have hnot : ¬ ∃ u r s : ℤ,
      z = (u : K) + (r : K) * pb.gen +
        (s : K) * ((1 + (1 : K) * pb.gen +
          (1 : K) * (pb.gen ^ 2 / (1 : K))) / 3) := by
    rintro ⟨u, r, s, heq⟩
    have heq' : (3 : K) * pb.gen ^ 2 =
        (2 : K) * ((3 * (u : K) + (s : K)) +
          (3 * (r : K) + (s : K)) * pb.gen +
          (s : K) * pb.gen ^ 2) := by
      have h6 := congrArg (fun x : K => (6 : K) * x) heq
      dsimp [z] at h6
      convert h6 using 1 <;> norm_num <;> ring
    have heq'' : (3 : ℚ) • pb.gen ^ 2 = (2 : ℚ) •
        (((3 * (u : ℚ) + (s : ℚ)) • (1 : K)) +
          ((3 * (r : ℚ) + (s : ℚ)) • pb.gen) +
          ((s : ℚ) • pb.gen ^ 2)) := by
      convert heq' using 1 <;> norm_num [Algebra.smul_def]
    have hc := congrArg (fun x : K => b.coord 2 x) heq''
    simp only [map_add, map_smul] at hc
    have hc' : (3 : ℚ) = (2 : ℚ) * (s : ℚ) := by
      simpa [hcoord0, hcoord1, hcoord2] using hc
    have hs : (2 : ℤ) * s = 3 := by exact_mod_cast hc'.symm
    omega
  intro h
  have hbad := h (K := K) (pb := pb) (h3 := h3)
    10 1 1 1 0 1 hm hn hv hroot hcubic hcv 2 hp hlocal z hzint hpz
  exact hnot hbad

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by exact pure_cubic_mixed_prime_saturation,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      change Unit at i
      cases i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      change Unit at j
      cases j
      exact (h rfl).elim
    · intro i
      change Empty at i
      exact nomatch i
  dependence := by
    intro i
    change Unit at i
    cases i
    dsimp [arena, signature] at *
    refine ⟨1, 0, 1, ?_⟩
    norm_num [actual, realize]

register_information_theorem pure_cubic_mixed_prime_saturation in arena
  readout via (realize signature
    (fun _ m n => m * n ^ 2) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Lattices.PureCubicMixedPrimeSaturation
    coordinates := #[6]
    readouts := #[{
      path := Array.replicate 15 "body" ++ #["domain", "arg", "arg"]
      stateBinder := 7 }] })
  escape continues (open)

#print axioms registration


end
end Reg.D5.S3.Arith.Lattices.PureCubicMixedPrimeSaturation

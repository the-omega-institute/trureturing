/- GID: D5/S3/Combinatorics/NumericalSemigroup/SignedResidueRelation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NumericalSemigroup/SignedResidueRelation
   mirror-E: none(waiver:general-signed-residue-relation)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Signed residue collisions give bounded relations on the original generators. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Tactic

/-! Finite signed residue arithmetic and its genuine reduced toric relation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.NumericalSemigroup.SignedResidueRelation
open scoped BigOperators

/-- Total positive mass of an integer vector. -/
def positiveMass {e : ℕ} (v : Fin e → ℤ) : ℕ := ∑ i, (v i).toNat

/-- Total negative mass of the same integer vector. -/
def negativeMass {e : ℕ} (v : Fin e → ℤ) : ℕ := ∑ i, (-v i).toNat

/-- The finite signed vectors with both masses at most q. -/
def signedVectors (e q : ℕ) : Finset (Fin e → ℤ) := by
  classical
  exact (Fintype.piFinset fun _ => Finset.Icc (-(q : ℤ)) q).filter
    (fun v => positiveMass v ≤ q ∧ negativeMass v ≤ q)

private theorem mem_signedVectors_iff (e q : ℕ) (v : Fin e → ℤ) :
    v ∈ signedVectors e q ↔ positiveMass v ≤ q ∧ negativeMass v ≤ q := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    have hp : (v i).toNat ≤ positiveMass v :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (v j).toNat) (Finset.mem_univ i)
    have hn : (-v i).toNat ≤ negativeMass v :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (-v j).toNat) (Finset.mem_univ i)
    apply Finset.mem_Icc.mpr
    omega

/-- A collision is converted to disjoint nonnegative exponents on the same generators. -/
theorem bounded_residue_relation (e q m : ℕ) (hm : 0 < m) (g : Fin e → ℕ)
    (hcard : m < (signedVectors e q).card) :
    ∃ a b : Fin e → ℕ, a ≠ b ∧ (∀ i, a i = 0 ∨ b i = 0) ∧
      (∑ i, a i) ≤ 2 * q ∧ (∑ i, b i) ≤ 2 * q ∧
      (∑ i, a i * g i) ≡ (∑ i, b i * g i) [MOD m] := by
  classical
  let : NeZero m := ⟨by omega⟩
  let residue : (Fin e → ℤ) → ZMod m := fun v => ∑ i, (v i : ZMod m) * g i
  have hc : (Finset.univ : Finset (ZMod m)).card < (signedVectors e q).card := by
    simpa [ZMod.card] using hcard
  obtain ⟨v, hv, w, hw, hvw, hres⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc
      (f := residue) (fun _ _ => Finset.mem_univ _)
  have hvb := (mem_signedVectors_iff e q v).mp hv
  have hwb := (mem_signedVectors_iff e q w).mp hw
  let a : Fin e → ℕ := fun i => (v i - w i).toNat
  let b : Fin e → ℕ := fun i => (w i - v i).toNat
  have hdiff (i : Fin e) : (a i : ℤ) - b i = v i - w i := by
    dsimp [a, b]
    omega
  have ha (i : Fin e) : a i ≤ (v i).toNat + (-w i).toNat := by
    dsimp [a]
    omega
  have hb (i : Fin e) : b i ≤ (w i).toNat + (-v i).toNat := by
    dsimp [b]
    omega
  refine ⟨a, b, ?_, ?_, ?_, ?_, ?_⟩
  · intro hab
    apply hvw
    funext i
    have := hdiff i
    rw [hab] at this
    omega
  · intro i
    dsimp [a, b]
    omega
  · have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin e))) => ha i)
    rw [Finset.sum_add_distrib] at h
    change (∑ i, a i) ≤ positiveMass v + negativeMass w at h
    omega
  · have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin e))) => hb i)
    rw [Finset.sum_add_distrib] at h
    change (∑ i, b i) ≤ positiveMass w + negativeMass v at h
    omega
  · apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    have hd : (∑ i, (a i : ZMod m) * g i) - (∑ i, (b i : ZMod m) * g i) = 0 := by
      rw [← Finset.sum_sub_distrib]
      calc
        _ = ∑ i, ((v i : ZMod m) - (w i : ZMod m)) * g i := by
          apply Finset.sum_congr rfl
          intro i _
          have hi := congrArg (fun z : ℤ => (z : ZMod m)) (hdiff i)
          push_cast at hi
          rw [← sub_mul, hi]
        _ = residue v - residue w := by
          simp only [residue, sub_mul, Finset.sum_sub_distrib]
        _ = 0 := sub_eq_zero.mpr hres
    simpa only [Nat.cast_sum, Nat.cast_mul] using sub_eq_zero.mp hd

/-- A monomial with the specified exponent vector. -/
def vectorMonomial {e : ℕ} (a : Fin e → ℕ) : MvPolynomial (Fin e) ℚ :=
  MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm a) 1

/-- The polynomial presentation map on the actual multiplicity and generators. -/
def semigroupMap {e : ℕ} (m : ℕ) (g : Fin e → ℕ) :
    MvPolynomial (Option (Fin e)) ℚ →+* MvPolynomial Unit ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun j => MvPolynomial.X () ^ (j.elim m g))

/-- Set the multiplicity variable to zero, retaining every other generator. -/
def reduction (e : ℕ) : MvPolynomial (Option (Fin e)) ℚ →+* MvPolynomial (Fin e) ℚ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun j => j.elim 0 MvPolynomial.X)

/-- The image of the genuine toric kernel under this reduction. -/
def reducedToricIdeal {e : ℕ} (m : ℕ) (g : Fin e → ℕ) : Ideal (MvPolynomial (Fin e) ℚ) :=
  Ideal.map (reduction e) (RingHom.ker (semigroupMap m g))

/-- The oriented relation before killing the multiplicity variable. -/
def toricRelation {e : ℕ} (a b : Fin e → ℕ) (l : ℕ) :
    MvPolynomial (Option (Fin e)) ℚ :=
  MvPolynomial.rename some (vectorMonomial a) -
    MvPolynomial.X none ^ l * MvPolynomial.rename some (vectorMonomial b)

private theorem monomial_image {e : ℕ} (a g : Fin e → ℕ) :
    (vectorMonomial a).eval₂ MvPolynomial.C (fun i => MvPolynomial.X () ^ g i) =
      (MvPolynomial.X () : MvPolynomial Unit ℚ) ^ (∑ i, a i * g i) := by
  rw [vectorMonomial, MvPolynomial.eval₂_monomial, map_one, one_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  simp_rw [← pow_mul, Nat.mul_comm (g _) (a _)]
  exact Finset.prod_pow_eq_pow_sum _ _ _

private theorem relation_image {e : ℕ} (m l : ℕ) (g a b : Fin e → ℕ)
    (h : (∑ i, a i * g i) = (∑ i, b i * g i) + m * l) :
    semigroupMap m g (toricRelation a b l) = 0 := by
  simp only [toricRelation, map_sub, map_mul, map_pow, semigroupMap,
    MvPolynomial.eval₂Hom_X', Option.elim_none, MvPolynomial.eval₂Hom_rename]
  change (vectorMonomial a).eval₂ MvPolynomial.C (fun i => MvPolynomial.X () ^ g i) -
    ((MvPolynomial.X () : MvPolynomial Unit ℚ) ^ m) ^ l *
      (vectorMonomial b).eval₂ MvPolynomial.C (fun i => MvPolynomial.X () ^ g i) = 0
  rw [monomial_image, monomial_image, ← pow_mul, ← pow_add, h, Nat.add_comm]
  exact sub_self _

private theorem relation_reduction {e : ℕ} (a b : Fin e → ℕ) (l : ℕ) :
    reduction e (toricRelation a b l) =
      vectorMonomial a - if l = 0 then vectorMonomial b else 0 := by
  change (toricRelation a b l).eval₂ MvPolynomial.C
    (fun j => j.elim 0 MvPolynomial.X) = _
  rw [toricRelation, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X,
    MvPolynomial.eval₂_rename, MvPolynomial.eval₂_rename]
  change (vectorMonomial a).eval₂ MvPolynomial.C MvPolynomial.X -
    (0 : MvPolynomial (Fin e) ℚ) ^ l *
      (vectorMonomial b).eval₂ MvPolynomial.C MvPolynomial.X = _
  rw [MvPolynomial.eval₂_eta, MvPolynomial.eval₂_eta]
  by_cases hl : l = 0 <;> simp [hl]

private theorem reduced_relation_nonzero {e : ℕ} (a b : Fin e → ℕ) (l : ℕ)
    (hab : a ≠ b) : reduction e (toricRelation a b l) ≠ 0 := by
  rw [relation_reduction]
  by_cases hl : l = 0
  · simp only [hl, ite_true, sub_ne_zero]
    intro h
    apply hab
    have hs := MvPolynomial.monomial_left_injective (R := ℚ) (by norm_num : (1 : ℚ) ≠ 0) h
    exact congrArg (fun f : Fin e →₀ ℕ => (f : Fin e → ℕ)) hs
  · simp [hl, vectorMonomial]

private theorem reduced_relation_degree {e : ℕ} (a b : Fin e → ℕ) (l d : ℕ)
    (ha : (∑ i, a i) ≤ d) (hb : (∑ i, b i) ≤ d) :
    (reduction e (toricRelation a b l)).totalDegree ≤ d := by
  have hdeg (c : Fin e → ℕ) : (vectorMonomial c).totalDegree = ∑ i, c i := by
    rw [vectorMonomial, MvPolynomial.totalDegree_monomial _ (by norm_num)]
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    rfl
  rw [relation_reduction]
  by_cases hl : l = 0
  · simp only [hl, ite_true]
    exact (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simpa [hdeg] using ha)
      (by simpa [hdeg] using hb))
  · simpa [hl, hdeg] using ha

/-- Pigeonhole in the actual residue group supplies a nonzero reduced toric relation
    of degree at most twice the signed mass bound. No realization is assumed. -/
theorem exists_bounded_reduced_relation (e q m : ℕ) (hm : 0 < m) (g : Fin e → ℕ)
    (hcard : m < (signedVectors e q).card) :
    ∃ f : MvPolynomial (Fin e) ℚ,
      f ∈ reducedToricIdeal m g ∧ f ≠ 0 ∧ f.totalDegree ≤ 2 * q := by
  obtain ⟨a, b, hab, _, ha, hb, hmod⟩ := bounded_residue_relation e q m hm g hcard
  have horient (a b : Fin e → ℕ) (hab : a ≠ b)
      (ha : (∑ i, a i) ≤ 2 * q) (hb : (∑ i, b i) ≤ 2 * q)
      (hmod : (∑ i, a i * g i) ≡ (∑ i, b i * g i) [MOD m])
      (hle : (∑ i, b i * g i) ≤ (∑ i, a i * g i)) :
      ∃ f : MvPolynomial (Fin e) ℚ,
        f ∈ reducedToricIdeal m g ∧ f ≠ 0 ∧ f.totalDegree ≤ 2 * q := by
    obtain ⟨l, hl⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hmod.symm
    refine ⟨reduction e (toricRelation a b l), ?_, reduced_relation_nonzero a b l hab,
      reduced_relation_degree a b l (2 * q) ha hb⟩
    apply Ideal.mem_map_of_mem
    exact relation_image m l g a b hl
  rcases le_total (∑ i, b i * g i) (∑ i, a i * g i) with hle | hle
  · exact horient a b hab ha hb hmod hle
  · exact horient b a (Ne.symm hab) hb ha hmod.symm hle

end D5.S3.Combinatorics.NumericalSemigroup.SignedResidueRelation

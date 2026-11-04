/- GID: D5/S3/VertexAlgebra/FormalSeries/SupportedBalancedCollision
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/SupportedBalancedCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: First-pair cross clearing and legal native balanced substitution. -/
import D5.S3.VertexAlgebra.FormalSeries.SupportedMiddleCollision
import Batteries.Tactic.OpenPrivate

/-! Consumed finite polynomial and native-series helpers for the actual balanced
transport. No substitution on a raw distribution is defined. The supported
binomial suppliers retain their Carnahan attribution.
proof_shape: bind-only; consumed by actual_three_field_balanced_transport. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.SupportedBalancedCollision
open SupportedChannelSeries SupportedThreeFieldCollision SupportedMiddleCollision
open UngradedLocalWordSeries UniformGradedLocalCorrelator
open scoped BigOperators
noncomputable section
open private pair_power_apply from
  D5.S3.VertexAlgebra.FormalSeries.SupportedThreeFieldCollision

/-- The two cross factors (y-z)^k(x-z)^k, with original labels fixed. -/
def balancedCross {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (F : Distribution 3 V) (y x z : ℤ) : V :=
  ∑ p ∈ Finset.range (k + 1), ∑ q ∈ Finset.range (k + 1),
    (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
      ((((-1 : ℂ) ^ q) * (k.choose q : ℂ)) •
        F ![y - k + p, x - k + q, z - p - q])

private theorem balanced_cross_action {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (F : Distribution 3 V) (e : Exponent 3) :
    polynomialAction (pairPolynomial 0 2 ^ k * pairPolynomial 1 2 ^ k) F e =
      balancedCross k F (e 0) (e 1) (e 2) := by
  rw [map_mul, Module.End.mul_apply, pair_power_apply]
  unfold balancedCross
  apply Finset.sum_congr rfl
  intro p hp
  have hpk : p ≤ k := by simpa using Finset.mem_range.mp hp
  rw [pair_power_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hqk : q ≤ k := by simpa using Finset.mem_range.mp hq
  apply congrArg (fun d : Exponent 3 =>
    (((-1 : ℂ) ^ p) * (k.choose p : ℂ)) •
      ((((-1 : ℂ) ^ q) * (k.choose q : ℂ)) • F d))
  funext i
  fin_cases i <;>
    simp [Pi.sub_apply, Pi.single_apply, nsmul_eq_mul,
      Int.natCast_sub hpk, Int.natCast_sub hqk] <;> omega

/-- The original Q, clearing the first pair after its two cross factors. -/
private theorem balanced_clearing_three {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : ℕ) (F : Distribution 3 V) (e : Exponent 3) :
    polynomialAction (clearingPolynomial 3 k) F e =
      clear k (fun y x => balancedCross k F y x (e 2)) (e 0) (e 1) := by
  classical
  have pairs : labelledPairs 3 = {(0, 1), (0, 2), (1, 2)} := by
    ext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> decide
  have poly : clearingPolynomial 3 k =
      pairPolynomial 0 1 ^ k * (pairPolynomial 0 2 ^ k * pairPolynomial 1 2 ^ k) := by
    simp [clearingPolynomial, pairs, mul_comm, mul_left_comm, mul_assoc]
  rw [poly, map_mul, Module.End.mul_apply, pair_power_apply]
  unfold clear
  apply Finset.sum_congr rfl
  intro p hp
  have hpk : p ≤ k := by simpa using Finset.mem_range.mp hp
  rw [balanced_cross_action]
  congr 1
  congr 1 <;>
    simp [Pi.sub_apply, Pi.single_apply, nsmul_eq_mul, Int.natCast_sub hpk] <;> omega

private def swap12 : Fin 3 ≃ Fin 3 := Equiv.swap 1 2

private theorem swap_index (s x z : ℕ) :
    (index3 s z x).embDomain swap12.toEmbedding = index3 s x z := by
  simp [index3, Finsupp.embDomain_eq_mapDomain, Finsupp.mapDomain_add,
    Finsupp.mapDomain_single, swap12, Equiv.swap_apply_def, add_comm, add_left_comm, add_assoc]

private theorem swap_signed {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (s x z : ℤ) :
    signedExtend (MvPowerSeries.rename swap12 P) ![s, x, z] =
      signedExtend P ![s, z, x] := by
  classical
  have nn : (∀ i : Fin 3, 0 ≤ (![s, x, z] : Fin 3 → ℤ) i) ↔
      (∀ i : Fin 3, 0 ≤ (![s, z, x] : Fin 3 → ℤ) i) := by
    constructor <;> intro h i <;> fin_cases i
    · exact h 0
    · exact h 2
    · exact h 1
    · exact h 0
    · exact h 2
    · exact h 1
  by_cases h : ∀ i : Fin 3, 0 ≤ (![s, x, z] : Fin 3 → ℤ) i
  · rw [signedExtend, if_pos h, signedExtend, if_pos (nn.mp h)]
    have idx (a b c : ℤ) : signedIndex (![a, b, c] : Fin 3 → ℤ) =
        index3 a.toNat b.toNat c.toNat := by
      ext i
      fin_cases i <;> simp [signedIndex, index3]
    rw [idx, idx, ← swap_index s.toNat x.toNat z.toNat]
    exact MvPowerSeries.coeff_embDomain_rename swap12.toEmbedding P _
  · simp only [signedExtend, if_neg h, if_neg (fun h' => h (nn.mpr h'))]

/-- Native positive substitution of the original numerator at [s+x,x,z]. -/
def balancedArguments (R : Type*) [CommRing R] : Fin 3 → MvPowerSeries (Fin 3) R :=
  ![MvPowerSeries.X 0 + MvPowerSeries.X 1, MvPowerSeries.X 1, MvPowerSeries.X 2]

def balancedCollision {R : Type*} [CommRing R] (P : MvPowerSeries (Fin 3) R) :
    MvPowerSeries (Fin 3) R := MvPowerSeries.subst (balancedArguments R) P

def balancedSlice {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (z : ℤ) : MvPowerSeries (Fin 2) R :=
  middleNativeSlice (MvPowerSeries.rename swap12 P) z

private theorem balancedSlice_extend {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (z y x : ℤ) :
    extend (balancedSlice P z) y x = signedExtend P ![y, x, z] := by
  rw [balancedSlice, middleNativeSlice_extend, swap_signed]

private theorem balanced_as_swapped_outer {R : Type*} [CommRing R]
    (P : MvPowerSeries (Fin 3) R) :
    balancedCollision P = MvPowerSeries.rename swap12
      (MvPowerSeries.subst (outerArguments R) (MvPowerSeries.rename swap12 P)) := by
  let r : Fin 3 → MvPowerSeries (Fin 3) R := MvPowerSeries.X ∘ swap12
  have hr : MvPowerSeries.HasSubst r := MvPowerSeries.HasSubst.X_comp _
  have ho : MvPowerSeries.HasSubst (outerArguments R) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro i
    fin_cases i <;> simp [outerArguments]
  have hc : MvPowerSeries.HasSubst
      (fun i => MvPowerSeries.subst (outerArguments R) (r i)) := by
    simpa only [MvPowerSeries.substAlgHom_apply] using hr.comp ho
  rw [MvPowerSeries.rename_eq_subst, MvPowerSeries.rename_eq_subst]
  change _ = MvPowerSeries.subst r (MvPowerSeries.subst (outerArguments R)
    (MvPowerSeries.subst r P))
  rw [MvPowerSeries.subst_comp_subst_apply hr ho,
    MvPowerSeries.subst_comp_subst_apply hc hr]
  unfold balancedCollision
  congr 1
  funext i
  simp only [r, Function.comp_apply, MvPowerSeries.subst_X ho]
  fin_cases i
  · change MvPowerSeries.X 0 + MvPowerSeries.X 1 =
      MvPowerSeries.subst r (MvPowerSeries.X 0 + MvPowerSeries.X 2)
    rw [MvPowerSeries.subst_add hr, MvPowerSeries.subst_X hr, MvPowerSeries.subst_X hr]
    simp [r, swap12, Equiv.swap_apply_def]
  · change MvPowerSeries.X 1 = MvPowerSeries.subst r (MvPowerSeries.X 2)
    rw [MvPowerSeries.subst_X hr]
    simp [r, swap12, Equiv.swap_apply_def]
  · change MvPowerSeries.X 2 = MvPowerSeries.subst r (MvPowerSeries.X 1)
    rw [MvPowerSeries.subst_X hr]
    simp [r, swap12, Equiv.swap_apply_def]

private theorem balancedCollision_signed {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (s x z : ℤ) :
    signedExtend (balancedCollision P) ![s, x, z] =
      extend (collision (balancedSlice P z)) s x := by
  rw [balanced_as_swapped_outer, swap_signed]
  exact outerCollision_signed (MvPowerSeries.rename swap12 P) z s x
end
end D5.S3.VertexAlgebra.SupportedBalancedCollision

/- GID: D5/S3/FiniteGroups/Cyclic/P48pNormalFactorReducibility
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/Cyclic/P48pNormalFactorReducibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reducibility from the characteristic prime-order subgroups of a normal P48p factor. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qPrimeToThreeReducibility
import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands

/-!
For the P48p obstruction, the normal factor is constrained by the order of
SL₂(F₂₃). The index bound accommodates the two order readings of Nebe
(arXiv:1212.0865, Theorem 3.6). Fixed-space information on the lattice
representation is supplied as explicit hypotheses.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace ExtremalC48

open private exists_normal_zpowers_of_dvd exists_invariant_subspace_of_card_lt from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qPrimeToThreeReducibility

variable {H V : Type*} [Group H] [Finite H] [AddCommGroup V] [Module ℚ V]

/-- A normal factor whose Sylow count is forced to be one has a characteristic
cyclic subgroup of order `p`. Its image is normal in the ambient group. -/
private theorem exists_ambient_normal_zpowers_of_dvd
    (K : Subgroup H) [K.Normal] (p m : ℕ) [Fact p.Prime]
    (hcard : Nat.card K ∣ p * m) (hp : p ∣ Nat.card K) (hpm : ¬ p ∣ m)
    (hSylow : ∀ n ∈ m.divisors, n ≡ 1 [MOD p] → n = 1) :
    ∃ x : K, orderOf x = p ∧ (Subgroup.zpowers (x : H)).Normal := by
  obtain ⟨x, hx, hn⟩ := exists_normal_zpowers_of_dvd p m hcard hp hpm hSylow
  have hcardx : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
  have hindex : ¬ p ∣ (Subgroup.zpowers x).index := by
    intro hd
    apply hpm
    apply (Nat.mul_dvd_mul_iff_left (show p.Prime from Fact.out).pos).mp
    calc
      p * p ∣ p * (Subgroup.zpowers x).index := Nat.mul_dvd_mul_left p hd
      _ = Nat.card K := by rw [← hcardx, Subgroup.card_mul_index]
      _ ∣ p * m := hcard
  have hP : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by simpa using hcardx)
  let P := hP.toSylow hindex
  let : (Subgroup.zpowers x).Characteristic := P.characteristic_of_normal hn
  have hnormal : ((Subgroup.zpowers x).map K.subtype).Normal := inferInstance
  rw [MonoidHom.map_zpowers] at hnormal
  exact ⟨x, hx, hnormal⟩

omit [Finite H] in
private theorem exists_invariant_subspace_of_normal_fixed_space
    (ρ : Representation ℚ H V) (x : H) [(Subgroup.zpowers x).Normal]
    (hzero : LinearMap.ker (ρ x - 1) ≠ ⊥)
    (hproper : LinearMap.ker (ρ x - 1) ≠ ⊤) :
    ∃ W : Submodule ℚ V, W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g, W ≤ W.comap (ρ g) := by
  let S := Subgroup.zpowers x
  let y : S := ⟨x, Subgroup.mem_zpowers x⟩
  let W := Representation.invariants (ρ.comp S.subtype)
  have hgen (s : S) : s ∈ Subgroup.zpowers y := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp s.property
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩
  have hW : W = LinearMap.ker (ρ x - 1) := by
    ext v
    rw [Representation.mem_invariants_iff_of_forall_mem_zpowers _ y hgen,
      LinearMap.mem_ker]
    change ρ x v = v ↔ ρ x v - v = 0
    exact sub_eq_zero.symm
  exact ⟨W, hW.symm ▸ hzero, hW.symm ▸ hproper, Representation.le_comap_invariants ρ S⟩

private theorem exists_invariant_subspace_of_normal_factor_prime
    (K : Subgroup H) [K.Normal] (ρ : Representation ℚ H V)
    (p m : ℕ) [Fact p.Prime]
    (hcard : Nat.card K ∣ p * m) (hp : p ∣ Nat.card K) (hpm : ¬ p ∣ m)
    (hSylow : ∀ n ∈ m.divisors, n ≡ 1 [MOD p] → n = 1)
    (hfix : ∀ x : K, orderOf x = p →
      LinearMap.ker (ρ (x : H) - 1) ≠ ⊥ ∧ LinearMap.ker (ρ (x : H) - 1) ≠ ⊤) :
    ∃ W : Submodule ℚ V, W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g, W ≤ W.comap (ρ g) := by
  obtain ⟨x, hx, hn⟩ := exists_ambient_normal_zpowers_of_dvd K p m hcard hp hpm hSylow
  let := hn
  exact exists_invariant_subspace_of_normal_fixed_space ρ (x : H)
    (hfix x hx).1 (hfix x hx).2

/-- An odd normal P48p factor forces reducibility in rational dimension 48,
including the trivial-factor case when the ambient group has order at most 12. -/
theorem p48p_odd_normal_factor_exists_invariant_subspace
    (K : Subgroup H) [K.Normal] (ρ : Representation ℚ H V)
    (hdim : Module.finrank ℚ V = 48)
    (hcard : Nat.card K ∣ 2 ^ 4 * 3 * 11 * 23) (hindex : K.index ∣ 12)
    (hodd : ¬ 2 ∣ Nat.card K)
    (hfix : ∀ x : K, (orderOf x = 3 ∨ orderOf x = 11 ∨ orderOf x = 23) →
      LinearMap.ker (ρ (x : H) - 1) ≠ ⊥ ∧ LinearMap.ker (ρ (x : H) - 1) ≠ ⊤) :
    ∃ W : Submodule ℚ V, W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g, W ≤ W.comap (ρ g) := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hcard' : Nat.card K ∣ 3 * 11 * 23 :=
    (Nat.prime_two.coprime_pow_of_not_dvd (m := 4) hodd).dvd_of_dvd_mul_left
      (by simpa only [Nat.mul_assoc] using hcard)
  by_cases h23 : 23 ∣ Nat.card K
  · exact exists_invariant_subspace_of_normal_factor_prime K ρ 23 33 hcard' h23
      (by decide) (by decide) (fun x hx => hfix x (Or.inr (Or.inr hx)))
  have hcop23 := ((show (23 : ℕ).Prime from Fact.out).coprime_iff_not_dvd.mpr h23).symm
  have hcard'' : Nat.card K ∣ 3 * 11 := hcop23.dvd_of_dvd_mul_right hcard'
  by_cases h11 : 11 ∣ Nat.card K
  · exact exists_invariant_subspace_of_normal_factor_prime K ρ 11 3 hcard'' h11
      (by decide) (by decide) (fun x hx => hfix x (Or.inr (Or.inl hx)))
  have hcop11 := ((show (11 : ℕ).Prime from Fact.out).coprime_iff_not_dvd.mpr h11).symm
  have hcard''' : Nat.card K ∣ 3 := hcop11.dvd_of_dvd_mul_right hcard''
  rcases (Nat.dvd_prime Nat.prime_three).mp hcard''' with hK | hK
  · have hH : Nat.card H = K.index := by
      rw [← K.card_mul_index, hK, one_mul]
    have hsmall : Nat.card H ≤ 12 := by
      rw [hH]
      exact Nat.le_of_dvd (by decide) hindex
    exact exists_invariant_subspace_of_card_lt ρ (by omega)
  · exact exists_invariant_subspace_of_normal_factor_prime K ρ 3 1 hcard'''
      (by rw [hK]) (by decide) (by decide) (fun x hx => hfix x (Or.inl hx))

/-- For a normal P48p factor of order prime to three, either of the divisors
11 or 23 forces an ambient invariant space through a characteristic Sylow subgroup. -/
theorem p48p_prime_to_three_normal_factor_exists_invariant_subspace
    (K : Subgroup H) [K.Normal] (ρ : Representation ℚ H V)
    (hcard : Nat.card K ∣ 2 ^ 4 * 3 * 11 * 23)
    (h3 : ¬ 3 ∣ Nat.card K) (hdiv : 11 ∣ Nat.card K ∨ 23 ∣ Nat.card K)
    (hfix : ∀ x : K, (orderOf x = 11 ∨ orderOf x = 23) →
      LinearMap.ker (ρ (x : H) - 1) ≠ ⊥ ∧ LinearMap.ker (ρ (x : H) - 1) ≠ ⊤) :
    ∃ W : Submodule ℚ V, W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g, W ≤ W.comap (ρ g) := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hcop3 := (Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm
  have hcard' : Nat.card K ∣ 2 ^ 4 * 11 * 23 :=
    hcop3.dvd_of_dvd_mul_right (by
      simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcard)
  by_cases h23 : 23 ∣ Nat.card K
  · exact exists_invariant_subspace_of_normal_factor_prime K ρ 23 176 hcard' h23
      (by decide) (by decide) (fun x hx => hfix x (Or.inr hx))
  have hcop23 := ((show (23 : ℕ).Prime from Fact.out).coprime_iff_not_dvd.mpr h23).symm
  have hcard'' : Nat.card K ∣ 2 ^ 4 * 11 := hcop23.dvd_of_dvd_mul_right hcard'
  exact exists_invariant_subspace_of_normal_factor_prime K ρ 11 16 hcard''
    (hdiv.resolve_right h23) (by decide) (by decide) (fun x hx => hfix x (Or.inl hx))

/-- If the pure cubic class has fixed rank sixteen, the absence of such a
cubic and ambient irreducibility force the normal factor's order to be a
power of two, of exponent at most four. -/
theorem p48p_irreducible_normal_factor_card_power_of_two
    (K : Subgroup H) [K.Normal] (ρ : Representation ℚ H V)
    (hcard : Nat.card K ∣ 2 ^ 4 * 3 * 11 * 23)
    (hfix : ∀ x : K, (orderOf x = 11 ∨ orderOf x = 23) →
      LinearMap.ker (ρ (x : H) - 1) ≠ ⊥ ∧ LinearMap.ker (ρ (x : H) - 1) ≠ ⊤)
    (hcubic : ∀ x : K, orderOf x = 3 → Module.finrank ℚ (LinearMap.ker (ρ (x : H) - 1)) = 16)
    (hno : ¬ ∃ x : K, orderOf x = 3 ∧ Module.finrank ℚ (LinearMap.ker (ρ (x : H) - 1)) = 16)
    (hirred : ¬ ∃ W : Submodule ℚ V, W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g, W ≤ W.comap (ρ g)) :
    ∃ n ≤ 4, Nat.card K = 2 ^ n := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h3 : ¬ 3 ∣ Nat.card K := by
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 hd
    exact hno ⟨x, hx, hcubic x hx⟩
  have hdiv : ¬ (11 ∣ Nat.card K ∨ 23 ∣ Nat.card K) := fun hd =>
    hirred (p48p_prime_to_three_normal_factor_exists_invariant_subspace K ρ hcard h3 hd hfix)
  have hcop23 := ((show (23 : ℕ).Prime by decide).coprime_iff_not_dvd.mpr
    (fun hd => hdiv (Or.inr hd))).symm
  have hcop11 := ((show (11 : ℕ).Prime by decide).coprime_iff_not_dvd.mpr
    (fun hd => hdiv (Or.inl hd))).symm
  have hcop3 := (Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm
  have hcard' : Nat.card K ∣ 2 ^ 4 * 3 * 11 := hcop23.dvd_of_dvd_mul_right hcard
  have hcard'' : Nat.card K ∣ 2 ^ 4 * 3 := hcop11.dvd_of_dvd_mul_right hcard'
  exact (Nat.dvd_prime_pow Nat.prime_two).mp (hcop3.dvd_of_dvd_mul_right hcard'')

local notation "SL23" => Matrix.SpecialLinearGroup (Fin 2) (ZMod 23)

/-- The only element of order two in SL₂(F₂₃) is the negative identity. -/
theorem p48p_sl23_orderTwo_eq_neg_one (A : SL23) (hA : orderOf A = 2) :
    A = -(1 : SL23) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  obtain ⟨hsq, hne⟩ := orderOf_eq_prime_iff.mp hA
  have hinv : A⁻¹ = A := by
    calc
      A⁻¹ = A⁻¹ * (A * A) := by rw [← pow_two, hsq, mul_one]
      _ = A := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hEntries : !![A 1 1, -A 0 1; -A 1 0, A 0 0] =
      (A : Matrix (Fin 2) (Fin 2) (ZMod 23)) := by
    rw [← Matrix.adjugate_fin_two, ← Matrix.SpecialLinearGroup.coe_inv, hinv]
  have h00 : A 1 1 = A 0 0 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod 23) => M 0 0) hEntries
  have eq_zero_of_neg_eq (a : ZMod 23) (ha : -a = a) : a = 0 := by
    have h : (2 : ZMod 23) * a = 0 := calc
      2 * a = a + a := two_mul a
      _ = -a + a := congrArg (· + a) ha.symm
      _ = 0 := neg_add_cancel a
    exact (mul_eq_zero.mp h).resolve_left (by decide)
  have h01 : A 0 1 = 0 := eq_zero_of_neg_eq _
    (congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod 23) => M 0 1) hEntries)
  have h10 : A 1 0 = 0 := eq_zero_of_neg_eq _
    (congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod 23) => M 1 0) hEntries)
  have hd : A 0 0 ^ 2 = 1 := by
    simpa only [Matrix.det_fin_two, h00, h01, h10, zero_mul, sub_zero, pow_two]
      using A.property
  have hScalar (d : ZMod 23) (he : A 0 0 = d) :
      (A : Matrix (Fin 2) (Fin 2) (ZMod 23)) = d • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [smul_eq_mul, h00, h01, h10, he]
  rcases sq_eq_one_iff.mp hd with he | he
  · exact (hne (Subtype.ext (by simpa using hScalar 1 he))).elim
  · apply Subtype.ext
    simpa only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, neg_smul,
      one_smul] using hScalar (-1) he

/-- A finite factor embedded into SL₂(F₂₃) with image avoiding the negative
identity has odd order. -/
theorem p48p_factor_odd_of_sl23_embedding_avoids_neg_one
    (K : Subgroup H) (φ : K →* SL23) (hφ : Function.Injective φ)
    (hneg : -(1 : SL23) ∉ φ.range) :
    ¬ 2 ∣ Nat.card K := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 hd
  have horder : orderOf (φ x) = 2 := (orderOf_injective φ hφ x).trans hx
  exact hneg ⟨x, p48p_sl23_orderTwo_eq_neg_one (φ x) horder⟩

#print axioms p48p_odd_normal_factor_exists_invariant_subspace
#print axioms p48p_prime_to_three_normal_factor_exists_invariant_subspace
#print axioms p48p_irreducible_normal_factor_card_power_of_two
#print axioms p48p_sl23_orderTwo_eq_neg_one
#print axioms p48p_factor_odd_of_sl23_embedding_avoids_neg_one

end ExtremalC48

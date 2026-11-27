/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qPrimeToThreeReducibility
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qPrimeToThreeReducibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational reducibility for the prime-to-three subgroups of SL₂(F₄₇). -/

/- Source: Library/VertexAlgebra/nebe2014extremal48.md. -/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.Divisors
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import OmegaBuild.Commands

/-!
Nebe (arXiv:1312.3780, Table 1) identifies the automorphism group of the
extremal lattice P48q with `SL₂(F₄₇)`. Every faithful rational action in
dimension 48 of a subgroup of order coprime to three has a nonzero proper
invariant subspace. This gives the representation-theoretic input for the
untwisted weight-two obstruction in the c = 48 extremal VOA problem.
-/

compile_only_with_mathlib

public section

set_option autoImplicit false

namespace ExtremalC48

open Module Polynomial

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℚ V]

/-- A prime-period rational endomorphism with no nonzero fixed vector makes the
space a module over the corresponding cyclotomic field. -/
theorem prime_sub_one_dvd_finrank_of_ker_sub_one_eq_bot
    (p : ℕ) [Fact p.Prime] (T : Module.End ℚ V) (hT : T ^ p = 1)
    (hker : LinearMap.ker (T - 1) = ⊥) : p - 1 ∣ finrank ℚ V := by
  let f := cyclotomic p ℚ
  have hprod : (T - 1) * aeval T f = 0 := by
    have hpoly : (X - 1) * f = X ^ p - 1 :=
      (mul_comm _ _).trans (cyclotomic_prime_mul_X_sub_one ℚ p)
    simpa [hT] using congrArg (aeval T : ℚ[X] →ₐ[ℚ] Module.End ℚ V) hpoly
  have hzero : aeval T f = 0 := by
    ext v
    apply (LinearMap.ker_eq_bot.mp hker)
    simpa only [Module.End.mul_apply, LinearMap.zero_apply, map_zero] using
      LinearMap.congr_fun hprod v
  let : Fact (Irreducible f) := ⟨cyclotomic.irreducible_rat (Fact.out : p.Prime).pos⟩
  have hspan : Ideal.span {f} ≤ RingHom.ker (aeval T).toRingHom := by
    rwa [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
  let φ : AdjoinRoot f →ₐ[ℚ] Module.End ℚ V :=
    Ideal.Quotient.liftₐ (Ideal.span {f}) (aeval T) fun _ h => RingHom.mem_ker.mp (hspan h)
  let : Module (AdjoinRoot f) V := Module.compHom V φ.toRingHom
  let : IsScalarTower ℚ (AdjoinRoot f) V :=
    IsScalarTower.of_algebraMap_smul fun r v => by
      change φ (algebraMap ℚ (AdjoinRoot f) r) v = r • v
      rw [φ.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
  have hdegree : finrank ℚ (AdjoinRoot f) = p - 1 := by
    calc
      finrank ℚ (AdjoinRoot f) = f.natDegree := finrank_quotient_span_eq_natDegree
      _ = p - 1 := (natDegree_cyclotomic p ℚ).trans (Nat.totient_prime Fact.out)
  rw [← hdegree]
  exact Module.finrank_dvd_finrank_right ℚ (AdjoinRoot f) V

private theorem exists_normal_zpowers_of_dvd [Finite G] (p m : ℕ) [Fact p.Prime]
    (hcard : Nat.card G ∣ p * m) (hp : p ∣ Nat.card G) (hpm : ¬ p ∣ m)
    (hSylow : ∀ n ∈ m.divisors, n ≡ 1 [MOD p] → n = 1) :
    ∃ x : G, orderOf x = p ∧ (Subgroup.zpowers x).Normal := by
  have hprime : p.Prime := Fact.out
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) p hp
  have hfactor : (Nat.card G).factorization p = 1 := by
    have hlower := (hprime.dvd_iff_one_le_factorization Nat.card_pos.ne').mp hp
    have hupper : ¬ 2 ≤ (Nat.card G).factorization p := by
      intro h
      have hd := (hprime.pow_dvd_iff_le_factorization Nat.card_pos.ne').mpr h
      exact hpm ((Nat.mul_dvd_mul_iff_left hprime.pos).mp (by
        simpa only [pow_two] using hd.trans hcard))
    omega
  let P := Sylow.ofCard (Subgroup.zpowers x) (p := p) (by
    rw [Nat.card_zpowers, hx, hfactor, pow_one])
  let : Finite (Sylow p G) := P.finite_of_finiteIndex
  have hindex : (Subgroup.zpowers x).index ∣ m := by
    apply (Nat.mul_dvd_mul_iff_left hprime.pos).mp
    have hmul : p * (Subgroup.zpowers x).index = Nat.card G := by
      rw [← hx, ← Nat.card_zpowers, Subgroup.card_mul_index]
    rwa [hmul]
  have hcount : Nat.card (Sylow p G) ∣ m := P.card_dvd_index.trans hindex
  have hm : m ≠ 0 := fun h => hpm (h ▸ dvd_zero p)
  have hunique := hSylow _ (Nat.mem_divisors.mpr ⟨hcount, hm⟩) (card_sylow_modEq_one p G)
  let : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp hunique).1
  exact ⟨x, hx, P.normal_of_subsingleton⟩

/-- A group of order dividing the prime-to-three part of `|SL₂(F₄₇)|`
has order at most 32 or a cyclic normal subgroup of order 23 or 47. -/
theorem card_le_32_or_exists_normal_zpowers [Finite G]
    (hcard : Nat.card G ∣ 32 * 23 * 47) :
    Nat.card G ≤ 32 ∨ ∃ x : G, (orderOf x = 23 ∨ orderOf x = 47) ∧
      (Subgroup.zpowers x).Normal := by
  let : Fact (Nat.Prime 47) := ⟨by decide⟩
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  by_cases h47 : 47 ∣ Nat.card G
  · obtain ⟨x, hx, hn⟩ := exists_normal_zpowers_of_dvd 47 736 hcard h47 (by decide)
      (by decide)
    exact Or.inr ⟨x, Or.inr hx, hn⟩
  have hcop47 := ((show (47 : ℕ).Prime from Fact.out).coprime_iff_not_dvd.mpr h47).symm
  have hcard' : Nat.card G ∣ 32 * 23 := hcop47.dvd_of_dvd_mul_right hcard
  by_cases h23 : 23 ∣ Nat.card G
  · obtain ⟨x, hx, hn⟩ := exists_normal_zpowers_of_dvd 23 32 hcard' h23 (by decide)
      (by decide)
    exact Or.inr ⟨x, Or.inl hx, hn⟩
  have hcop23 := ((show (23 : ℕ).Prime from Fact.out).coprime_iff_not_dvd.mpr h23).symm
  have hd : Nat.card G ∣ 32 := hcop23.dvd_of_dvd_mul_right hcard'
  exact Or.inl (Nat.le_of_dvd (by decide) hd)

private theorem exists_invariant_subspace_of_card_lt [Finite G]
    (ρ : Representation ℚ G V) (hcard : Nat.card G < finrank ℚ V) :
    ∃ W : Submodule ℚ V, W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g, W ≤ W.comap (ρ g) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (lt_of_le_of_lt (Nat.zero_le _) hcard)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let W := Submodule.span ℚ (Set.range fun g => ρ g v)
  refine ⟨W, ?_, ?_, ?_⟩
  · intro h
    have hm : v ∈ W := Submodule.subset_span ⟨1, by simp⟩
    rw [h, Submodule.mem_bot] at hm
    exact hv hm
  · intro h
    have hle := finrank_le_of_span_eq_top h
    rw [← Nat.card_eq_fintype_card] at hle
    exact (not_le_of_gt hcard) hle
  · intro g
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨g * k, by simp [Module.End.mul_apply]⟩

private theorem exists_invariant_subspace_of_normal_zpowers
    (ρ : Representation ℚ G V) (hρ : Function.Injective ρ) (x : G)
    [(Subgroup.zpowers x).Normal] (p : ℕ) [Fact p.Prime] (hx : orderOf x = p)
    (hd : ¬ (p - 1) ∣ finrank ℚ V) :
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
  refine ⟨W, ?_, ?_, Representation.le_comap_invariants ρ S⟩
  · intro h
    have hpow : (ρ x) ^ p = 1 := by
      rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
    exact hd (prime_sub_one_dvd_finrank_of_ker_sub_one_eq_bot p (ρ x) hpow (hW ▸ h))
  · intro h
    have hfix : ρ x = 1 := LinearMap.ext fun v => by
      have hv : v ∈ W := h.symm ▸ Submodule.mem_top
      exact hv y
    have heq : x = 1 := hρ (hfix.trans (map_one ρ).symm)
    rw [heq, orderOf_one] at hx
    exact (show p.Prime from Fact.out).ne_one hx.symm

/-- In rational dimension 48 a faithful representation of a group whose
order divides `32 * 23 * 47` has a nonzero proper invariant subspace. -/
theorem exists_invariant_subspace_of_card_dvd [Finite G]
    (ρ : Representation ℚ G V) (hρ : Function.Injective ρ) (hdim : finrank ℚ V = 48)
    (hcard : Nat.card G ∣ 32 * 23 * 47) :
    ∃ W : Submodule ℚ V, W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g, W ≤ W.comap (ρ g) := by
  rcases card_le_32_or_exists_normal_zpowers hcard with hsmall | ⟨x, hx, hnormal⟩
  · exact exists_invariant_subspace_of_card_lt ρ (by omega)
  · let := hnormal
    rcases hx with hx | hx
    · let : Fact (Nat.Prime 23) := ⟨by decide⟩
      exact exists_invariant_subspace_of_normal_zpowers ρ hρ x 23 hx (hdim.symm ▸ (by decide))
    · let : Fact (Nat.Prime 47) := ⟨by decide⟩
      exact exists_invariant_subspace_of_normal_zpowers ρ hρ x 47 hx (hdim.symm ▸ (by decide))

/-- Every faithful rational representation of dimension 48 of a
prime-to-three subgroup of `SL₂(F₄₇)` is reducible. -/
theorem sl47_prime_to_three_exists_invariant_subspace
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 47)))
    (hH : ¬ 3 ∣ Nat.card H)
    (ρ : Representation ℚ H V) (hρ : Function.Injective ρ) (hdim : finrank ℚ V = 48) :
    ∃ W : Submodule ℚ V, W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g, W ≤ W.comap (ρ g) := by
  let : Fact (Nat.Prime 47) := ⟨by decide⟩
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 47)) = (32 * 23 * 47) * 3 := by
    have h := Matrix.card_SL_field (𝔽 := ZMod 47) 2
    rw [Fin.prod_univ_two, ZMod.card] at h
    exact h.trans (by decide)
  have hd : Nat.card H ∣ (32 * 23 * 47) * 3 := hSL ▸ H.card_subgroup_dvd_card
  have hcop := (Nat.prime_three.coprime_iff_not_dvd.mpr hH).symm
  exact exists_invariant_subspace_of_card_dvd ρ hρ hdim (hcop.dvd_of_dvd_mul_right hd)

#print axioms sl47_prime_to_three_exists_invariant_subspace

end ExtremalC48

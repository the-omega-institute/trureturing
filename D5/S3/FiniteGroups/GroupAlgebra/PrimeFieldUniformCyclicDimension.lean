/- GID: D5/S3/FiniteGroups/GroupAlgebra/PrimeFieldUniformCyclicDimension
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/PrimeFieldUniformCyclicDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.GroupAction.Quotient, mathlib/module/Mathlib.FieldTheory.Finiteness]
   utility: none
   digest: Actual cyclic projectivity over the prime field forces finrank at least r*p for C_p^r. -/

import D5.S3.FiniteGroups.GroupAlgebra.PGroupProjectiveNormRing
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

/-!
The public norm criterion gives surjectivity of each actual cyclic norm.
Ordinary field-module projectivity supplies a linear section, and the public
norm-section equivalence gives d = p * finrank(cyclic invariants).
Stabilizer containment identifies these invariants with the actual fixedBy
set for the representation action on V. Burnside's lemma on this finite set
then forces r <= d/p. No faithfulness or choice of a cyclic-free basis is
assumed. Every private declaration below is consumed by the public endpoint.
-/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.GroupAlgebra.PrimeFieldUniformCyclicDimension

open scoped MonoidAlgebra

universe uV

section Helpers

private abbrev E (p r : ℕ) := Multiplicative (Fin r → ZMod p)

variable {p r : ℕ} [Fact p.Prime]
variable {V : Type uV} [AddCommGroup V] [Module (ZMod p) V]

-- This is the actual underlying-set action, on the vectors themselves.
@[instance_reducible]
private def vectorAction (ρ : Representation (ZMod p) (E p r) V) :
    MulAction (E p r) V where
  smul g v := ρ g v
  one_smul v := by
    change ρ 1 v = v
    rw [map_one]
    rfl
  mul_smul g h v := by
    change ρ (g * h) v = ρ g (ρ h v)
    rw [map_mul]
    rfl

private theorem elementary_pow (g : E p r) : g ^ p = 1 := by
  have h : p • g.toAdd = 0 := by
    funext i
    change p • g.toAdd i = 0
    simp [nsmul_eq_mul]
  simpa only [ofAdd_nsmul, ofAdd_toAdd,
    ofAdd_zero] using congrArg Multiplicative.ofAdd h

private theorem actual_order (g : E p r) (hg : g ≠ 1) : orderOf g = p :=
  orderOf_eq_prime (elementary_pow g) hg

-- A vector fixed by g is fixed by its actual cyclic subgroup: the whole
-- subgroup lies in the stabilizer. This does not inspect powers of rho(g).
private theorem cyclic_mem_invariants_iff
    (ρ : Representation (ZMod p) (E p r) V) (g : E p r) (v : V) :
    v ∈ (Representation.invariants (ρ.comp (Subgroup.zpowers g).subtype)) ↔ ρ g v = v := by
  let : MulAction (E p r) V := vectorAction ρ
  constructor
  · intro hv
    exact (Representation.mem_invariants _ v).mp hv ⟨g, Subgroup.mem_zpowers g⟩
  · intro hv
    have hgv : g ∈ MulAction.stabilizer (E p r) v := hv
    have hle : Subgroup.zpowers g ≤ MulAction.stabilizer (E p r) v :=
      Subgroup.zpowers_le.mpr hgv
    apply (Representation.mem_invariants _ v).mpr
    intro h
    exact (MulAction.mem_stabilizer_iff).mp (hle h.property)

variable [FiniteDimensional (ZMod p) V]

private theorem cyclic_finrank (ρ : Representation (ZMod p) (E p r) V)
    (g : E p r) (hg : g ≠ 1)
    (hproj : Module.Projective (ZMod p)[Subgroup.zpowers g]
      (Representation.asModule (ρ.comp (Subgroup.zpowers g).subtype))) :
    Module.finrank (ZMod p) V =
      p * Module.finrank (ZMod p)
        (Representation.invariants (ρ.comp (Subgroup.zpowers g).subtype)) := by
  classical
  let σ : Representation (ZMod p) (Subgroup.zpowers g) V :=
    ρ.comp (Subgroup.zpowers g).subtype
  have hcard : Fintype.card (Subgroup.zpowers g) = p := by
    rw [Fintype.card_zpowers, actual_order g hg]
  have hP : IsPGroup p (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_eq_fintype_card, hcard, pow_one])
  have hN :=
    (PGroupProjectiveNormRing.projective_iff_projective_invariants_and_norm_surjective
      p 1 (by decide) (by simp) hP σ).mp hproj
  let N : V →ₗ[ZMod p] σ.invariants :=
    LinearMap.codRestrict σ.invariants σ.norm (fun v =>
      (Representation.mem_invariants σ _).mpr
        (fun h => Representation.self_norm_apply σ h v))
  have hNsurj : Function.Surjective N := by
    intro w
    obtain ⟨v, hv⟩ := hN.2 w
    exact ⟨v, Subtype.ext hv⟩
  -- Every vector space is free, hence projective over its coefficient field.
  -- This is ordinary field-module projectivity, not a local-free assumption.
  let : Module.Projective (ZMod p) σ.invariants := inferInstance
  obtain ⟨L, hL⟩ := Module.projective_lifting_property N
    (LinearMap.id : σ.invariants →ₗ[ZMod p] σ.invariants) hNsurj
  have hsection (w : σ.invariants) : σ.norm (L w) = (w : V) :=
    congrArg (fun z : σ.invariants => (z : V)) (LinearMap.congr_fun hL w)
  obtain ⟨e, _⟩ :=
    PGroupProjectiveNormRing.exists_equivariant_linearEquiv_of_norm_section
      p 1 (by decide) (by simp) hP σ L hsection
  calc
    Module.finrank (ZMod p) V =
        Module.finrank (ZMod p) (Subgroup.zpowers g → σ.invariants) := e.finrank_eq
    _ = p * Module.finrank (ZMod p) σ.invariants := by
      rw [Module.finrank_pi_fintype]
      simp [hcard]

private theorem fixedBy_natCard (ρ : Representation (ZMod p) (E p r) V)
    (g : E p r) (hg : g ≠ 1)
    (hproj : Module.Projective (ZMod p)[Subgroup.zpowers g]
      (Representation.asModule (ρ.comp (Subgroup.zpowers g).subtype)))
    (n : ℕ) (hd : Module.finrank (ZMod p) V = p * n) :
    let : MulAction (E p r) V := vectorAction ρ
    Nat.card (MulAction.fixedBy V g) = p ^ n := by
  let : MulAction (E p r) V := vectorAction ρ
  let σ : Representation (ZMod p) (Subgroup.zpowers g) V :=
    ρ.comp (Subgroup.zpowers g).subtype
  have hdim := cyclic_finrank ρ g hg hproj
  have hw : Module.finrank (ZMod p) σ.invariants = n :=
    Nat.mul_left_cancel (Fact.out : p.Prime).pos (hdim.symm.trans hd)
  let e : σ.invariants ≃ MulAction.fixedBy V g :=
    { toFun := fun w => ⟨(w : V), (cyclic_mem_invariants_iff ρ g w).mp w.property⟩
      invFun := fun w => ⟨(w : V), (cyclic_mem_invariants_iff ρ g w).mpr w.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let : Fintype σ.invariants :=
    Module.fintypeOfFintype (Module.finBasis (ZMod p) σ.invariants)
  calc
    Nat.card (MulAction.fixedBy V g) = Nat.card σ.invariants := (Nat.card_congr e).symm
    _ = Fintype.card σ.invariants := Nat.card_eq_fintype_card
    _ = Fintype.card (ZMod p) ^ Module.finrank (ZMod p) σ.invariants :=
      Module.card_eq_pow_finrank
    _ = p ^ n := by rw [ZMod.card, hw]

-- The arithmetic obstruction after the actual Burnside count. All
-- subtractions are natural subtractions; their positivity is supplied here.
private theorem rank_le_of_burnside_divisibility {p r n : ℕ}
    (hp : p.Prime) (hn : 0 < n)
    (hdiv : p ^ r ∣ p ^ (p * n) + (p ^ r - 1) * p ^ n) : r ≤ n := by
  let q := p ^ ((p - 1) * n)
  have hqpos : 0 < q := pow_pos hp.pos _
  have hrpos : 0 < p ^ r := pow_pos hp.pos _
  have hqone : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
  have hrone : p ^ r - 1 + 1 = p ^ r := Nat.sub_add_cancel (by omega)
  have hexp : p * n = n + (p - 1) * n := by
    calc
      p * n = (p - 1 + 1) * n := by rw [Nat.sub_add_cancel hp.one_le]
      _ = n + (p - 1) * n := by ring
  have hfactor : p ^ (p * n) = p ^ n * q := by rw [hexp, pow_add]
  have hA : p ^ n * q = p ^ n * (q - 1) + p ^ n := by
    calc
      p ^ n * q = p ^ n * (q - 1 + 1) := by rw [hqone]
      _ = p ^ n * (q - 1) + p ^ n := by ring
  have hB : p ^ r * p ^ n = (p ^ r - 1) * p ^ n + p ^ n := by
    calc
      p ^ r * p ^ n = (p ^ r - 1 + 1) * p ^ n := by rw [hrone]
      _ = (p ^ r - 1) * p ^ n + p ^ n := by ring
  have hshift : p ^ (p * n) + (p ^ r - 1) * p ^ n =
      p ^ n * (q - 1) + p ^ r * p ^ n := by
    rw [hfactor, hA, hB]
    omega
  have hfdiv : p ^ r ∣ p ^ n * (q - 1) := by
    rw [hshift] at hdiv
    exact (Nat.dvd_add_iff_left (dvd_mul_right (p ^ r) (p ^ n))).mpr hdiv
  have hmpos : 0 < (p - 1) * n :=
    Nat.mul_pos (by have := hp.two_le; omega) hn
  have hpdvd : p ∣ q := dvd_pow_self p (Nat.ne_of_gt hmpos)
  have hcop : Nat.Coprime p (q - 1) := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    apply hp.not_dvd_one
    apply (Nat.dvd_add_iff_right hd).mpr
    rwa [hqone]
  have hpow : p ^ r ∣ p ^ n := (hcop.pow_left r).dvd_of_dvd_mul_right hfdiv
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hpow

end Helpers

/-- For every prime (including 2) and every rank (including 0), a nonzero
finite-dimensional prime-field representation of the actual group C_p^r
which is projective on every actual cyclic subgroup has dimension at least r*p.
The vector-space universe is independent of the group's universe. -/
theorem rank_mul_prime_le_finrank_of_cyclic_projective
    (p r : ℕ) [Fact p.Prime]
    {V : Type uV} [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] [Nontrivial V]
    (ρ : Representation (ZMod p) (Multiplicative (Fin r → ZMod p)) V)
    (hproj : ∀ H : Subgroup (Multiplicative (Fin r → ZMod p)), IsCyclic H →
      Module.Projective (ZMod p)[H] (Representation.asModule (ρ.comp H.subtype))) :
    r * p ≤ Module.finrank (ZMod p) V := by
  classical
  by_cases hr : r = 0
  · subst r
    simp
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  let g₀ : E p r := Multiplicative.ofAdd (fun _ => (1 : ZMod p))
  have hg₀ : g₀ ≠ 1 := by
    intro h
    have hi := congrArg (fun x : E p r => x.toAdd ⟨0, hrpos⟩) h
    have hz : (1 : ZMod p) = 0 := by simpa only [g₀, toAdd_ofAdd,
      toAdd_one, Pi.zero_apply] using hi
    exact one_ne_zero hz
  let n := Module.finrank (ZMod p) (Representation.invariants (ρ.comp (Subgroup.zpowers g₀).subtype))
  have hd : Module.finrank (ZMod p) V = p * n :=
    cyclic_finrank ρ g₀ hg₀ (hproj _ inferInstance)
  have hdpos : 0 < Module.finrank (ZMod p) V := Module.finrank_pos
  have hn : 0 < n := by
    by_contra h
    have hz : n = 0 := by omega
    rw [hd, hz, mul_zero] at hdpos
    omega
  let : Fintype V := Module.fintypeOfFintype (Module.finBasis (ZMod p) V)
  let : MulAction (E p r) V := vectorAction ρ
  let : Fintype (Quotient (MulAction.orbitRel (E p r) V)) := Fintype.ofFinite _
  have hcard : Fintype.card (E p r) = p ^ r := by
    rw [Fintype.card_multiplicative, Fintype.card_pi_const, ZMod.card]
  let e₁ : MulAction.fixedBy V (1 : E p r) ≃ V :=
    { toFun := Subtype.val
      invFun := fun v => ⟨v, one_smul (E p r) v⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfix_one : Fintype.card (MulAction.fixedBy V (1 : E p r)) =
      p ^ Module.finrank (ZMod p) V := by
    calc
      _ = Fintype.card V := Fintype.card_congr e₁
      _ = _ := by rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hfix (g : E p r) (hg : g ≠ 1) :
      Fintype.card (MulAction.fixedBy V g) = p ^ n := by
    have h := fixedBy_natCard ρ g hg (hproj _ inferInstance) n hd
    simpa only [Nat.card_eq_fintype_card] using h
  have hsum : (∑ g : E p r, Fintype.card (MulAction.fixedBy V g)) =
      p ^ (p * n) + (p ^ r - 1) * p ^ n := by
    calc
      _ = Fintype.card (MulAction.fixedBy V (1 : E p r)) +
          ∑ g ∈ (Finset.univ.erase (1 : E p r)),
            Fintype.card (MulAction.fixedBy V g) :=
        (Finset.add_sum_erase Finset.univ
          (fun g : E p r => Fintype.card (MulAction.fixedBy V g))
          (Finset.mem_univ (1 : E p r))).symm
      _ = p ^ (p * n) + ∑ _g ∈ (Finset.univ.erase (1 : E p r)), p ^ n := by
        rw [hfix_one, hd]
        apply congrArg (fun t : ℕ => p ^ (p * n) + t)
        apply Finset.sum_congr rfl
        intro g hg
        exact hfix g (Finset.ne_of_mem_erase hg)
      _ = _ := by
        simp [Finset.sum_const, nsmul_eq_mul,
          Finset.card_erase_of_mem (Finset.mem_univ (1 : E p r)), hcard]
  have hBurnside := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (E p r) V
  have hdiv : p ^ r ∣ p ^ (p * n) + (p ^ r - 1) * p ^ n := by
    have h : Fintype.card (E p r) ∣
        ∑ g : E p r, Fintype.card (MulAction.fixedBy V g) := by
      refine ⟨Fintype.card (Quotient (MulAction.orbitRel (E p r) V)), ?_⟩
      exact hBurnside.trans (Nat.mul_comm _ _)
    simpa only [hcard, hsum] using h
  have hrn := rank_le_of_burnside_divisibility (Fact.out : p.Prime) hn hdiv
  calc
    r * p ≤ n * p := Nat.mul_le_mul_right p hrn
    _ = Module.finrank (ZMod p) V := (Nat.mul_comm n p).trans hd.symm

end D5.S3.FiniteGroups.GroupAlgebra.PrimeFieldUniformCyclicDimension

/- GID: D5/S3/FiniteGroups/GroupAlgebra/PrimeFieldCyclicProjectivityDimension
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/PrimeFieldCyclicProjectivityDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Trace, mathlib/module/Mathlib.RingTheory.Polynomial.Cyclotomic.Expand]
   utility: none
   digest: A nonzero prime-field representation of C_p × C_p projective on every actual cyclic subgroup has dimension at least 2p. -/

import D5.S3.FiniteGroups.GroupAlgebra.ProjectiveConjugationTrace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
For a nonzero finite-dimensional representation over the prime field,
projectivity on all actual cyclic subgroups forces dimension at least 2p.
The proof uses a nilpotent chain basis and the prime-field coefficient
of a commuting operator to select an actual cyclic direction.

All group restrictions below are to actual subgroups. In particular the
order of (a,1) is computed in the group, independently of its image.
Polynomial multiplication is evaluated without changing composition order.
The only polynomial cancellation used is already inside the imported
cyclotomic theorem; no endomorphism is cancelled.
-/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.GroupAlgebra.PrimeFieldCyclicProjectivityDimension

open scoped MonoidAlgebra
open Polynomial

universe uV

private abbrev E (p : ℕ) := Multiplicative (ZMod p × ZMod p)

variable {p : ℕ} [Fact p.Prime]
variable {V : Type uV} [AddCommGroup V] [Module (ZMod p) V]

private theorem elementary_pow (g : E p) : g ^ p = 1 := by
  have h : p • g.toAdd = 0 := by
    ext <;> simp [nsmul_eq_mul]
  simpa only [ofAdd_nsmul, ofAdd_toAdd,
    ofAdd_zero] using congrArg Multiplicative.ofAdd h

private theorem actual_order (g : E p) (hg : g ≠ 1) : orderOf g = p :=
  orderOf_eq_prime (elementary_pow g) hg

theorem geometric_norm_polynomial :
    (∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i) = (X - 1) ^ (p - 1) := by
  have hp : ¬p ∣ 1 := by
    exact fun h => (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp h)
  simpa only [one_mul, Polynomial.cyclotomic_one, Polynomial.cyclotomic_prime] using
    (Polynomial.cyclotomic_mul_prime_eq_pow_of_not_dvd (ZMod p) (n := 1) hp)

-- The equivalence enumerates the actual subgroup, including when rho g = 1.
private theorem actual_norm (ρ : Representation (ZMod p) (E p) V)
    (g : E p) (hg : orderOf g = p) :
    Representation.norm (ρ.comp (Subgroup.zpowers g).subtype) = (ρ g - 1) ^ (p - 1) := by
  classical
  let e := finEquivZPowers (isOfFinOrder_of_finite g)
  have hs : (∑ h : Subgroup.zpowers g, ρ (h : E p)) =
      ∑ i : Fin (orderOf g), ρ (g ^ (i : ℕ)) := by
    simpa only [e, finEquivZPowers_apply] using
      (e.sum_comp (fun h : Subgroup.zpowers g => ρ (h : E p))).symm
  rw [hg] at hs
  change (∑ h : Subgroup.zpowers g, ρ (h : E p)) = _
  calc
    _ = ∑ i : Fin p, (ρ g) ^ (i : ℕ) := by simpa only [map_pow] using hs
    _ = ∑ i ∈ Finset.range p, (ρ g) ^ i :=
      (Finset.sum_range (fun i : ℕ => (ρ g) ^ i)).symm
    _ = (ρ g - 1) ^ (p - 1) := by
      simpa only [map_sum, map_pow, map_sub, map_one, Polynomial.aeval_X] using
        congrArg (Polynomial.aeval (ρ g)) (geometric_norm_polynomial (p := p))

private theorem pow_apply_of_fixed (A : Module.End (ZMod p) V)
    (w : V) (hw : A w = w) (n : ℕ) : (A ^ n) w = w := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [pow_succ', Module.End.mul_apply, ih] using hw

private theorem actual_invariant (ρ : Representation (ZMod p) (E p) V)
    (g : E p) (w : V) (hw : ρ g w = w) :
    w ∈ Representation.invariants (ρ.comp (Subgroup.zpowers g).subtype) := by
  classical
  intro h
  let e := finEquivZPowers (isOfFinOrder_of_finite g)
  obtain ⟨i, rfl⟩ := e.surjective h
  change ρ (g ^ (i : ℕ)) w = w
  rw [map_pow]
  exact pow_apply_of_fixed (ρ g) w hw i

-- This is just the necessary half of the existing arbitrary-ring criterion.
private theorem cyclic_norm_preimage (ρ : Representation (ZMod p) (E p) V)
    (g : E p) (hg : orderOf g = p)
    (hproj : Module.Projective (ZMod p)[Subgroup.zpowers g]
      (Representation.asModule (ρ.comp (Subgroup.zpowers g).subtype)))
    (w : V) (hw : ρ g w = w) :
    ∃ v : V, ((ρ g - 1) ^ (p - 1)) v = w := by
  classical
  let σ : Representation (ZMod p) (Subgroup.zpowers g) V :=
    ρ.comp (Subgroup.zpowers g).subtype
  have hP : IsPGroup p (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_eq_fintype_card, Fintype.card_zpowers, hg, pow_one])
  have hN :=
    (PGroupProjectiveNormRing.projective_iff_projective_invariants_and_norm_surjective
      p 1 (by decide) (by simp) hP σ).mp hproj
  obtain ⟨v, hv⟩ := hN.2 ⟨w, actual_invariant ρ g w hw⟩
  refine ⟨v, ?_⟩
  simpa only [σ, actual_norm ρ g hg] using hv

private theorem operator_nilpotent (ρ : Representation (ZMod p) (E p) V)
    (g : E p) : (ρ g - 1) ^ p = 0 := by
  have hpow : (ρ g) ^ p = 1 := by rw [← map_pow, elementary_pow, map_one]
  have hpoly : ((X - 1 : (ZMod p)[X]) ^ p) = X ^ p - 1 :=
    by simpa only [one_pow] using sub_pow_char (X : (ZMod p)[X]) 1
  have h := congrArg (Polynomial.aeval (ρ g)) hpoly
  simpa only [map_pow, map_sub, map_one, Polynomial.aeval_X, hpow, one_pow,
    sub_self] using h

-- A least annihilating power supplies a nonzero fixed vector, without Jordan form.
private theorem nonzero_killed_vector [Nontrivial V]
    (N : Module.End (ZMod p) V) (hN : N ^ p = 0) :
    ∃ w : V, w ≠ 0 ∧ N w = 0 := by
  classical
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have hex : ∃ n : ℕ, (N ^ n) x = 0 := ⟨p, by rw [hN]; simp⟩
  let m := Nat.find hex
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    have hz := Nat.find_spec hex
    change (N ^ m) x = 0 at hz
    exact hx (by simpa only [hm0, pow_zero, Module.End.one_apply] using hz)
  refine ⟨(N ^ (m - 1)) x, ?_, ?_⟩
  · exact fun h => Nat.find_min hex (by change m - 1 < m; omega) h
  · change (N * N ^ (m - 1)) x = 0
    rw [← pow_succ']
    have hm' : m - 1 + 1 = m := by omega
    rw [hm']
    exact Nat.find_spec hex

-- The least nonzero coefficient isolates the top vector after applying a power.
private theorem chain_independent (N : Module.End (ZMod p) V)
    (hN : N ^ p = 0) (v : V) (hv : (N ^ (p - 1)) v ≠ 0) :
    LinearIndependent (ZMod p) (fun i : Fin p => (N ^ (i : ℕ)) v) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  by_contra hi
  have hex : ∃ j : ℕ, ∃ hj : j < p, c ⟨j, hj⟩ ≠ 0 := ⟨i, i.isLt, hi⟩
  let j := Nat.find hex
  obtain ⟨hjp, hjc⟩ := Nat.find_spec hex
  let jF : Fin p := ⟨j, hjp⟩
  have hlow (i : Fin p) (hij : (i : ℕ) < j) : c i = 0 := by
    by_contra hci
    exact Nat.find_min hex hij ⟨i.isLt, hci⟩
  have hzero :
      (∑ i : Fin p, c i • (N ^ (p - 1 - j + (i : ℕ))) v) = 0 := by
    have h := congrArg (fun z : V => (N ^ (p - 1 - j)) z) hc
    simpa only [map_sum, map_smul, ← Module.End.mul_apply, ← pow_add, map_zero] using h
  have hsingle :
      (∑ i : Fin p, c i • (N ^ (p - 1 - j + (i : ℕ))) v) =
        c jF • (N ^ (p - 1)) v := by
    calc
      _ = c jF • (N ^ (p - 1 - j + j)) v := by
        apply Finset.sum_eq_single jF
        · intro i _ hij
          by_cases hlt : (i : ℕ) < j
          · rw [hlow i hlt, zero_smul]
          · have hne : (i : ℕ) ≠ j := fun he => hij (Fin.ext he)
            have hp : p ≤ p - 1 - j + (i : ℕ) := by omega
            rw [pow_eq_zero_of_le hp hN]
            simp
        · simp
      _ = _ := by rw [show p - 1 - j + j = p - 1 by omega]
  have hcj : c jF = 0 :=
    (smul_eq_zero.mp (hsingle.symm.trans hzero)).resolve_right hv
  exact hjc hcj

private noncomputable def chainPolynomial (c : Fin p → ZMod p) : (ZMod p)[X] :=
  ∑ i : Fin p, C (c i) * X ^ (i : ℕ)

private theorem eval_chainPolynomial (N : Module.End (ZMod p) V)
    (c : Fin p → ZMod p) :
    Polynomial.aeval N (chainPolynomial c) = ∑ i : Fin p, c i • N ^ (i : ℕ) := by
  simp only [chainPolynomial, map_sum, map_mul, Polynomial.aeval_C, map_pow,
    Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

private theorem chain_polynomial_unique (N : Module.End (ZMod p) V)
    (v : V) (hli : LinearIndependent (ZMod p) (fun i : Fin p => (N ^ (i : ℕ)) v))
    {c d : Fin p → ZMod p}
    (h : Polynomial.aeval N (chainPolynomial c) = Polynomial.aeval N (chainPolynomial d)) :
    c = d := by
  classical
  have he := congrArg (fun A : Module.End (ZMod p) V => A v) h
  simp only [eval_chainPolynomial, LinearMap.sum_apply, LinearMap.smul_apply] at he
  have hz : ∑ i : Fin p, (c i - d i) • (N ^ (i : ℕ)) v = 0 := by
    simpa only [sub_smul, Finset.sum_sub_distrib] using sub_eq_zero.mpr he
  have hcoeff := Fintype.linearIndependent_iff.mp hli (fun i => c i - d i) hz
  funext i
  exact sub_eq_zero.mp (hcoeff i)

-- Independence plus dimension produces the basis; commutation is checked on it.
-- The unique coefficient function has values in ZMod p, not an extension field.
private theorem centralizer_polynomial [FiniteDimensional (ZMod p) V]
    (hd : Module.finrank (ZMod p) V = p)
    (N T : Module.End (ZMod p) V) (hN : N ^ p = 0)
    (v : V) (hv : (N ^ (p - 1)) v ≠ 0) (hTN : Commute T N) :
    ∃! c : Fin p → ZMod p, Polynomial.aeval N (chainPolynomial c) = T := by
  classical
  have hli := chain_independent N hN v hv
  let b : Module.Basis (Fin p) (ZMod p) V :=
    basisOfLinearIndependentOfCardEqFinrank'
      (fun i : Fin p => (N ^ (i : ℕ)) v) hli (by simpa using hd.symm)
  have hb (i : Fin p) : b i = (N ^ (i : ℕ)) v := by
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank']
  let c : Fin p → ZMod p := fun i => b.repr (T v) i
  have hTv : T v = ∑ i : Fin p, c i • (N ^ (i : ℕ)) v := by
    simpa only [c, hb] using (b.sum_repr (T v)).symm
  have hTsum : T = ∑ j : Fin p, c j • N ^ (j : ℕ) := by
    apply b.ext
    intro i
    rw [hb]
    calc
      T ((N ^ (i : ℕ)) v) = (N ^ (i : ℕ)) (T v) :=
        congrArg (fun A : Module.End (ZMod p) V => A v) (hTN.pow_right (i : ℕ)).eq
      _ = (N ^ (i : ℕ)) (∑ j : Fin p, c j • (N ^ (j : ℕ)) v) :=
        congrArg (N ^ (i : ℕ)) hTv
      _ = ∑ j : Fin p, c j • (N ^ ((i : ℕ) + (j : ℕ))) v := by
        simp only [map_sum, map_smul, ← Module.End.mul_apply, ← pow_add]
      _ = (∑ j : Fin p, c j • N ^ (j : ℕ)) ((N ^ (i : ℕ)) v) := by
        simp only [LinearMap.sum_apply, LinearMap.smul_apply,
          ← Module.End.mul_apply, ← pow_add]
        apply Finset.sum_congr rfl
        intro j _
        rw [Nat.add_comm]
  have hc : Polynomial.aeval N (chainPolynomial c) = T :=
    (eval_chainPolynomial N c).trans hTsum.symm
  refine ⟨c, hc, ?_⟩
  intro d hd'
  exact chain_polynomial_unique N v hli (hd'.trans hc.symm)

private theorem aeval_apply_of_killed (N : Module.End (ZMod p) V)
    (w : V) (hw : N w = 0) (f : (ZMod p)[X]) :
    Polynomial.aeval N f w = f.coeff 0 • w := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      simp only [map_add, LinearMap.add_apply, Polynomial.coeff_add, add_smul, hf, hg]
  | monomial n c =>
      cases n with
      | zero =>
          simp [Algebra.algebraMap_eq_smul_one]
      | succ n =>
          simp [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
            pow_succ, Module.End.mul_apply, hw]

-- Actual integer powers, not shifted operators: the first coefficient is k+b1.
private theorem prime_field_cancellation [FiniteDimensional (ZMod p) V]
    (hd : Module.finrank (ZMod p) V = p)
    (N T : Module.End (ZMod p) V) (hN : N ^ p = 0) (hT : T ^ p = 1)
    (v : V) (hv : (N ^ (p - 1)) v ≠ 0) (hTN : Commute T N) :
    ∃ a : ZMod p,
      (((1 + N) ^ a.val * T - 1) ^ (p - 1) = 0) ∧
        T ((N ^ (p - 1)) v) = (N ^ (p - 1)) v := by
  classical
  obtain ⟨c, hc, _⟩ := centralizer_polynomial hd N T hN v hv hTN
  let f : (ZMod p)[X] := chainPolynomial c
  have hf : Polynomial.aeval N f = T := hc
  let w := (N ^ (p - 1)) v
  have hw : w ≠ 0 := hv
  have hNw : N w = 0 := by
    change (N * N ^ (p - 1)) v = 0
    rw [← pow_succ', Nat.sub_add_cancel (Fact.out : p.Prime).pos]
    exact LinearMap.congr_fun hN v
  have hconstantpow : (f ^ p).coeff 0 = (f.coeff 0) ^ p :=
    map_pow Polynomial.constantCoeff f p
  have hscalar : f.coeff 0 • w = w := by
    have he : Polynomial.aeval N (f ^ p) w = w := by rw [map_pow, hf, hT]; rfl
    rw [aeval_apply_of_killed N w hNw, hconstantpow, ZMod.pow_card] at he
    exact he
  have hc0 : f.coeff 0 = 1 := by
    have hz : (f.coeff 0 - 1) • w = 0 := by
      rw [sub_smul, one_smul, hscalar, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hw)
  let a : ZMod p := -f.coeff 1
  let k : ℕ := a.val
  let P : (ZMod p)[X] := (1 + X) ^ k * f - 1
  have hpow0 : ((1 + X : (ZMod p)[X]) ^ k).coeff 0 = 1 := by
    simp [Polynomial.coeff_one_add_X_pow]
  have hpow1 : ((1 + X : (ZMod p)[X]) ^ k).coeff 1 = (k : ZMod p) := by
    simp [Polynomial.coeff_one_add_X_pow, Nat.choose_one_right]
  have hk : (k : ZMod p) = -f.coeff 1 := by
    exact ZMod.natCast_zmod_val a
  have hP0 : P.coeff 0 = 0 := by
    simp [P, Polynomial.mul_coeff_zero, hpow0, hc0]
  have hP1 : P.coeff 1 = 0 := by
    simp [P, Polynomial.mul_coeff_one, hpow0, hpow1, hc0, hk, Polynomial.coeff_one]
  have hdiv : (X : (ZMod p)[X]) ^ 2 ∣ P := by
    apply Polynomial.X_pow_dvd_iff.mpr
    intro j hj
    interval_cases j
    · exact hP0
    · exact hP1
  obtain ⟨q, hq⟩ := hdiv
  have hzero : Polynomial.aeval N (P ^ (p - 1)) = 0 := by
    calc
      _ = N ^ (2 * (p - 1)) * Polynomial.aeval N (q ^ (p - 1)) := by
        rw [hq, mul_pow, ← pow_mul]
        simp only [map_mul, map_pow, Polynomial.aeval_X]
      _ = 0 := by
        have hlarge : p ≤ 2 * (p - 1) := by
          have hp := (Fact.out : p.Prime).two_le
          omega
        rw [pow_eq_zero_of_le hlarge hN, zero_mul]
  refine ⟨a, ?_, ?_⟩
  · simpa only [P, k, map_pow, map_sub, map_mul, map_add, map_one,
      Polynomial.aeval_X, hf] using hzero
  · change T w = w
    rw [← hf, aeval_apply_of_killed N w hNw, hc0, one_smul]

private theorem prime_dvd_dimension [FiniteDimensional (ZMod p) V]
    (ρ : Representation (ZMod p) (E p) V) (g : E p) (hg : orderOf g = p)
    (hproj : Module.Projective (ZMod p)[Subgroup.zpowers g]
      (Representation.asModule (ρ.comp (Subgroup.zpowers g).subtype))) :
    p ∣ Module.finrank (ZMod p) V := by
  classical
  let σ : Representation (ZMod p) (Subgroup.zpowers g) V :=
    ρ.comp (Subgroup.zpowers g).subtype
  obtain ⟨_, D, hD⟩ :=
    (ProjectiveConjugationTrace.projective_iff_projective_and_conjugation_trace_one σ).mp hproj
  have htrace (x : Subgroup.zpowers g) :
      LinearMap.trace (ZMod p) V ((σ x).comp (D.comp (σ x⁻¹))) =
        LinearMap.trace (ZMod p) V D := by
    change LinearMap.trace (ZMod p) V (σ x * (D * σ x⁻¹)) = _
    rw [LinearMap.trace_mul_comm, mul_assoc, ← map_mul, inv_mul_cancel,
      map_one, mul_one]
  have hcard : Fintype.card (Subgroup.zpowers g) = p :=
    Fintype.card_zpowers.trans hg
  have h := congrArg (LinearMap.trace (ZMod p) V) hD
  rw [map_sum, LinearMap.trace_id] at h
  have hz : (Module.finrank (ZMod p) V : ZMod p) = 0 := by
    simpa only [htrace, Finset.sum_const, Finset.card_univ, hcard,
      nsmul_eq_mul, CharP.cast_eq_zero, zero_mul] using h.symm
  exact (ZMod.natCast_eq_zero_iff _ _).mp hz

/-- Every nonzero finite-dimensional prime-field representation of C_p × C_p
whose restriction to every actual cyclic subgroup is projective has dimension
at least 2p. This includes p=2 and representations with nontrivial kernel.
No faithfulness or prescribed normal form is assumed. -/
theorem two_mul_prime_le_finrank_of_cyclic_projective
    [FiniteDimensional (ZMod p) V] [Nontrivial V]
    (ρ : Representation (ZMod p) (Multiplicative (ZMod p × ZMod p)) V)
    (hcyc : ∀ H : Subgroup (Multiplicative (ZMod p × ZMod p)), IsCyclic H →
      Module.Projective (ZMod p)[H]
        (Representation.asModule
          (ρ.comp H.subtype : Representation (ZMod p) H V))) :
    2 * p ≤ Module.finrank (ZMod p) V := by
  classical
  let r : E p := Multiplicative.ofAdd (1, 0)
  let t : E p := Multiplicative.ofAdd (0, 1)
  have hrne : r ≠ 1 := by
    intro h
    have he := congrArg (fun g : E p => g.toAdd.1) h
    simp [r] at he
  have hr : orderOf r = p := actual_order r hrne
  have hrproj := hcyc (Subgroup.zpowers r) inferInstance
  have hdiv := prime_dvd_dimension ρ r hr hrproj
  by_contra hbound
  have hlt : Module.finrank (ZMod p) V < 2 * p := by omega
  have hpos : 0 < Module.finrank (ZMod p) V := Module.finrank_pos
  have hd : Module.finrank (ZMod p) V = p := by
    obtain ⟨m, hm⟩ := hdiv
    have hp := (Fact.out : p.Prime).pos
    have hmpos : 0 < m := by nlinarith
    have hmlt : m < 2 := by nlinarith
    have hm1 : m = 1 := by omega
    simpa only [hm1, mul_one] using hm
  let N : Module.End (ZMod p) V := ρ r - 1
  let T : Module.End (ZMod p) V := ρ t
  have hN : N ^ p = 0 := operator_nilpotent ρ r
  obtain ⟨w, hw, hNw⟩ := nonzero_killed_vector N hN
  have hrw : ρ r w = w := by
    have he : ρ r w - w = 0 := by
      simpa only [N, LinearMap.sub_apply, Module.End.one_apply] using hNw
    exact sub_eq_zero.mp he
  obtain ⟨v, hv⟩ := cyclic_norm_preimage ρ r hr hrproj w hrw
  have hvtop : (N ^ (p - 1)) v ≠ 0 := by
    change ((ρ r - 1) ^ (p - 1)) v ≠ 0
    rw [hv]
    exact hw
  have hT : T ^ p = 1 := by
    change (ρ t) ^ p = 1
    rw [← map_pow, elementary_pow, map_one]
  have hTN : Commute T N := by
    change ρ t * (ρ r - 1) = (ρ r - 1) * ρ t
    rw [mul_sub, sub_mul, mul_one, one_mul, ← ρ.map_mul, ← ρ.map_mul, mul_comm t r]
  obtain ⟨a, hcancel, hTtop⟩ := prime_field_cancellation hd N T hN hT v hvtop hTN
  let g : E p := Multiplicative.ofAdd (a, 1)
  have hgne : g ≠ 1 := by
    intro h
    have he := congrArg (fun x : E p => x.toAdd.2) h
    simp [g] at he
  have hg : orderOf g = p := actual_order g hgne
  have hactual : r ^ a.val * t = g := by
    change Multiplicative.ofAdd (1, 0) ^ a.val * Multiplicative.ofAdd (0, 1) =
      Multiplicative.ofAdd (a, 1)
    rw [← ofAdd_nsmul, ← ofAdd_add]
    congr 1
    ext <;> simp [nsmul_eq_mul]
  have hρg : ρ g = (ρ r) ^ a.val * T := by
    rw [← hactual, map_mul, map_pow]
  have hS : 1 + N = ρ r := by dsimp [N]; abel
  have hzero : (ρ g - 1) ^ (p - 1) = 0 := by
    rw [hρg]
    simpa only [hS] using hcancel
  let z := (N ^ (p - 1)) v
  have hz : z ≠ 0 := hvtop
  have hNz : N z = 0 := by
    change (N * N ^ (p - 1)) v = 0
    rw [← pow_succ', Nat.sub_add_cancel (Fact.out : p.Prime).pos]
    exact LinearMap.congr_fun hN v
  have hrz : ρ r z = z := by
    have he : ρ r z - z = 0 := by
      simpa only [N, LinearMap.sub_apply, Module.End.one_apply] using hNz
    exact sub_eq_zero.mp he
  have hgz : ρ g z = z := by
    have hTz : T z = z := hTtop
    rw [hρg, Module.End.mul_apply, hTz]
    exact pow_apply_of_fixed (ρ r) z hrz a.val
  have hgproj := hcyc (Subgroup.zpowers g) inferInstance
  obtain ⟨x, hx⟩ := cyclic_norm_preimage ρ g hg hgproj z hgz
  rw [hzero] at hx
  exact hz (by simpa only [LinearMap.zero_apply] using hx.symm)

end D5.S3.FiniteGroups.GroupAlgebra.PrimeFieldCyclicProjectivityDimension

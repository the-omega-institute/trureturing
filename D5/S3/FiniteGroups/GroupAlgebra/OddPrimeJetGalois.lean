/- GID: D5/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGalois
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/OddPrimeJetGalois
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.Solvable]
   utility: none
   digest: Actual original-label Galois projection and derived-series upper bounds. -/
import D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetRadicalGroup
import Mathlib.GroupTheory.Solvable

/-! The Galois projection is defined on actual original pairs; the derived-series
bounds do not require a section onto its image. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetTop
open Polynomial Module OddPrimeJetDeformation OddPrimeJetCommutant
open OddPrimeJetRadical OddPrimeJetRadicalGroup OddPrimeJetGroup FiniteJetCoefficients
open FiniteJetClassification
open scoped BigOperators commutatorElement
universe u
variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
variable {K : Type u} [Field K] [Algebra (ZMod p) K]
local notation "F" => ZMod p
local notation "V" => Polynomial.degreeLT K p

variable [Fintype K] {n : ℕ} (hn : 1 ≤ n) (hK : Fintype.card K = p^n)

private def originalLabelScalar (q : K →ₗ[F] K) (z : originalGroup (p := p) q) : K :=
  (z.val.2 (Multiplicative.ofAdd 1)).toAdd

private theorem originalLabelScalar_ne_zero (q : K →ₗ[F] K)
    (z : originalGroup (p := p) q) : originalLabelScalar q z ≠ 0 := by
  intro h
  have he : z.val.2 (Multiplicative.ofAdd 1) = z.val.2 1 := by
    apply Multiplicative.toAdd.injective
    rw [z.val.2.map_one]
    exact h
  have := congrArg Multiplicative.toAdd (z.val.2.injective he)
  exact one_ne_zero this

private theorem originalGalois_data (q : K →ₗ[F] K) (hq : q 1 = 0)
    (z : originalGroup (p := p) q) :
    ∃ σ : K ≃ₐ[F] K, ∀ a : K,
      (z.val.2 (Multiplicative.ofAdd a)).toAdd = originalLabelScalar q z * σ a := by
  obtain ⟨c, σ, δ, hφ, _⟩ :=
    (OddPrimeJetPairClassification.fixed_automorphism_intertwining_iff
      q q hq hq z.val.2).mp ⟨z.val.1, z.property⟩
  have hc : originalLabelScalar q z = (c : K) := by
    simpa only [originalLabelScalar, map_one, mul_one] using hφ 1
  exact ⟨σ, fun a => by rw [hc]; exact hφ a⟩

private def originalSigma (q : K →ₗ[F] K) (hq : q 1 = 0)
    (z : originalGroup (p := p) q) : K ≃ₐ[F] K :=
  (originalGalois_data q hq z).choose

private theorem originalGalois_formula (q : K →ₗ[F] K) (hq : q 1 = 0)
    (z : originalGroup (p := p) q) (a : K) :
    (z.val.2 (Multiplicative.ofAdd a)).toAdd =
      originalLabelScalar q z * originalSigma q hq z a :=
  (originalGalois_data q hq z).choose_spec a

private theorem originalLabelScalar_mul (q : K →ₗ[F] K) (hq : q 1 = 0)
    (z w : originalGroup (p := p) q) :
    originalLabelScalar q (z*w) =
      originalLabelScalar q z * originalSigma q hq z (originalLabelScalar q w) := by
  exact originalGalois_formula q hq z (originalLabelScalar q w)

/-- The actual Galois coordinate of the original additive label. Its defining
formula determines it uniquely, independently of any choice of lifts. -/
def originalGalois (q : K →ₗ[F] K) (hq : q 1 = 0) :
    originalGroup (p := p) q →* (K ≃ₐ[F] K) where
  toFun := originalSigma q hq
  map_one' := by
    ext a
    have h := originalGalois_formula q hq 1 a
    simpa [originalLabelScalar] using h.symm
  map_mul' z w := by
    ext a
    apply mul_left_cancel₀ (originalLabelScalar_ne_zero q (z*w))
    rw [← originalGalois_formula, originalLabelScalar_mul q hq]
    have h := originalGalois_formula q hq z
      ((w.val.2 (Multiplicative.ofAdd a)).toAdd)
    change ((z*w).val.2 (Multiplicative.ofAdd a)).toAdd = _ at h
    rw [originalGalois_formula q hq w a, map_mul] at h
    simpa only [AlgEquiv.mul_apply, mul_assoc] using h

private theorem originalGalois_eq_labelSigma (A : Fin (n-1) → K)
    (hq : Q (p := p) n A 1 = 0)
    (z : originalGroup (Q (p := p) n A)) :
    originalGalois (Q (p := p) n A) hq z =
      labelSigma hn hK A (project (Q (p := p) n A) z) := by
  ext a
  let s := project (Q (p := p) n A) z
  have hc : originalLabelScalar (Q (p := p) n A) z =
      (labelScalar hn hK A s : K) := by
    have h := label_formula hn hK A s 1
    change (z.val.2 (Multiplicative.ofAdd 1)).toAdd = _ at h
    simpa only [originalLabelScalar, map_one, mul_one] using h
  apply mul_left_cancel₀ (originalLabelScalar_ne_zero (Q (p := p) n A) z)
  calc
    _ = (z.val.2 (Multiplicative.ofAdd a)).toAdd :=
      (originalGalois_formula (Q (p := p) n A) hq z a).symm
    _ = _ := by rw [hc]; exact label_formula hn hK A s a

#print axioms originalGalois

private theorem coherentLift_constant (A : Fin (n-1) → K)
    (s : labelGroup (Q (p := p) n A)) (a : K) :
    coherentLift hn hK A s (constantLinear a) =
      constantLinear (labelSigma hn hK A s a) := by
  have hs (b x : K) : OddPrimeJetPairClassification.shear (p := p) b
      (constantLinear x) = constantLinear x := by
    change constantLinear x + b • OddPrimeJetPairClassification.topShear
      (constantLinear x) = constantLinear x
    have hz : OddPrimeJetPairClassification.topShear (p := p)
        (constantLinear (p := p) (K := K) x) = 0 := by
      simp only [OddPrimeJetPairClassification.topShear, LinearMap.comp_apply,
        pow_constant (p-1) (by have hp : 2 < p := Fact.out; omega), map_zero]
    rw [hz, smul_zero, add_zero]
  have hS (x : K) : canonicalShear (p := p) A (constantLinear x) = constantLinear x :=
    hs _ x
  have hSi (x : K) : (canonicalShear (p := p) A).symm (constantLinear x) =
      constantLinear x := by
    apply (canonicalShear (p := p) A).injective
    rw [LinearEquiv.apply_symm_apply, hS]
  change (canonicalShear A).symm
    (degreeLift hn hK A s (canonicalShear A (constantLinear a))) = _
  rw [hS, degreeLift_constant, hSi]

def originalConstantScalar (q : K →ₗ[F] K)
    (z : originalGroup (p := p) q) : K :=
  coefficientZero (z.val.1 (constantLinear 1))

include hn hK in
private theorem original_constant_action (q : K →ₗ[F] K) (hq : q 1 = 0)
    (z : originalGroup (p := p) q) (a : K) :
    z.val.1 (constantLinear a) =
      constantLinear (originalConstantScalar q z * originalGalois q hq z a) := by
  obtain ⟨A, hA⟩ := (coefficientMap_bijective hn hK).surjective ⟨q,hq⟩
  have he : Q (p := p) n A = q := congrArg Subtype.val hA
  subst q
  obtain ⟨⟨k,s⟩, hfac, _⟩ := unique_factorization hn hK A z
  have hs : project (Q (p := p) n A) z = s := by
    rw [← hfac, map_mul, project_section,
      show project (Q (p := p) n A) k.val = 1 from k.property, one_mul]
  obtain ⟨u, hu⟩ := (commutantUnitsEquiv (p := p) (Q (p := p) n A)).surjective k
  have hact (x : K) : z.val.1 (constantLinear x) =
      constantLinear (leadingHom (Q (p := p) n A) hq u.val * labelSigma hn hK A s x) := by
    rw [← hfac, ← hu]
    change u.val.val (coherentLift hn hK A s (constantLinear x)) = _
    rw [coherentLift_constant, constant_action _ hq]
    rfl
  have hc : originalConstantScalar (Q (p := p) n A) z =
      leadingHom (Q (p := p) n A) hq u.val := by
    dsimp only [originalConstantScalar]
    rw [hact]
    simp [coefficientZero, constantLinear]
  rw [hc, originalGalois_eq_labelSigma hn hK A hq, hs]
  exact hact a

include hn hK in
private def scalarKernelConstantHom (q : K →ₗ[F] K) (hq : q 1 = 0) :
    (originalGalois (p := p) q hq).ker →* K where
  toFun z := originalConstantScalar q z.val
  map_one' := by simp [originalConstantScalar, coefficientZero, constantLinear]
  map_mul' z w := by
    change coefficientZero (z.val.val.1 (w.val.val.1 (constantLinear 1))) = _
    rw [original_constant_action hn hK q hq w.val 1]
    simp only [map_one, mul_one]
    rw [original_constant_action hn hK q hq z.val]
    have hz : originalGalois q hq z.val = 1 := z.property
    rw [hz]
    simp [coefficientZero, constantLinear]

private def scalarKernelLabelHom (q : K →ₗ[F] K) (hq : q 1 = 0) :
    (originalGalois (p := p) q hq).ker →* K where
  toFun z := originalLabelScalar q z.val
  map_one' := rfl
  map_mul' z w := by
    have hz : originalSigma q hq z.val = 1 := z.property
    change originalLabelScalar q (z.val*w.val) = _
    rw [originalLabelScalar_mul q hq, hz, AlgEquiv.one_apply]

include hn hK in
private def scalarKernelPairHom (q : K →ₗ[F] K) (hq : q 1 = 0) :
    (originalGalois (p := p) q hq).ker →* (Kˣ × Kˣ) :=
  (scalarKernelConstantHom hn hK q hq).toHomUnits.prod
    (scalarKernelLabelHom q hq).toHomUnits

#print axioms scalarKernelPairHom

private def originalPrincipalUnits (q : K →ₗ[F] K) (hq : q 1 = 0) :
    Subgroup (originalGroup (p := p) q) :=
  (actualPrincipalUnits (p := p) q hq).map (project q).ker.subtype

include hn hK in
private theorem scalarKernel_pair_mem_principal (q : K →ₗ[F] K) (hq : q 1 = 0)
    (z : (originalGalois (p := p) q hq).ker)
    (hp : scalarKernelPairHom hn hK q hq z = 1) :
    z.val ∈ originalPrincipalUnits q hq := by
  have hc : originalConstantScalar q z.val = 1 :=
    congrArg (fun t : Kˣ × Kˣ => (t.1 : K)) hp
  have hl : originalLabelScalar q z.val = 1 :=
    congrArg (fun t : Kˣ × Kˣ => (t.2 : K)) hp
  have hσ : originalSigma q hq z.val = 1 := z.property
  have hφ : z.val.val.2 = 1 := by
    apply MulEquiv.ext
    intro a
    apply Multiplicative.toAdd.injective
    simpa [hl, hσ] using
      originalGalois_formula q hq z.val a.toAdd
  have hk : z.val ∈ (project q).ker := by
    change project q z.val = 1
    apply Subtype.ext
    exact hφ
  let k : (project q).ker := ⟨z.val, hk⟩
  obtain ⟨u, hu⟩ := (commutantUnitsEquiv (p := p) q).surjective k
  have hlead : leadingHom q hq u.val = 1 := by
    have he := congrArg (fun w : (project q).ker =>
      coefficientZero (w.val.val.1 (constantLinear 1))) hu
    change leadingHom q hq u.val = originalConstantScalar q z.val at he
    exact he.trans hc
  have hup : u ∈ principalUnits (p := p) q hq := by
    change Units.map (leadingHom q hq).toMonoidHom u = 1
    apply Units.ext
    exact hlead
  exact ⟨k, ⟨u, hup, hu⟩, rfl⟩

include hn hK in
private theorem scalar_commutator_mem_principal (q : K →ₗ[F] K) (hq : q 1 = 0)
    (x y : originalGroup (p := p) q)
    (hx : originalGalois q hq x = 1) (hy : originalGalois q hq y = 1) :
    ⁅x,y⁆ ∈ originalPrincipalUnits q hq := by
  let x' : (originalGalois q hq).ker := ⟨x,hx⟩
  let y' : (originalGalois q hq).ker := ⟨y,hy⟩
  have hp : scalarKernelPairHom hn hK q hq ⁅x',y'⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  exact scalarKernel_pair_mem_principal hn hK q hq ⁅x',y'⁆ hp

include hK in
private theorem originalPrincipalUnits_commute (q : K →ₗ[F] K) (hq : q 1 = 0)
    (x y : originalGroup (p := p) q)
    (hx : x ∈ originalPrincipalUnits q hq) (hy : y ∈ originalPrincipalUnits q hq) :
    x*y = y*x := by
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hy
  have h := (actual_principal_unit_structure q hq hK).1
    (⟨a,ha⟩ : actualPrincipalUnits q hq) (⟨b,hb⟩ : actualPrincipalUnits q hq)
  exact congrArg (fun z : actualPrincipalUnits q hq => z.val.val) h

include hK in
private theorem commutator_eq_bot_of_le_principal (q : K →ₗ[F] K) (hq : q 1 = 0)
    (H : Subgroup (originalGroup (p := p) q)) (hH : H ≤ originalPrincipalUnits q hq) :
    ⁅H,H⁆ = ⊥ := by
  apply le_antisymm _ bot_le
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    (originalPrincipalUnits_commute hK q hq x y (hH hx) (hH hy))

include hn hK in
/-- The actual original group has derived length at most three, without a
splitting of the actual label stabilizer onto its Galois image. -/
theorem original_derived_three_eq_bot (q : K →ₗ[F] K) (hq : q 1 = 0) :
    derivedSeries (originalGroup (p := p) q) 3 = ⊥ := by
  have hfirst : derivedSeries (originalGroup (p := p) q) 1 ≤
      (originalGalois q hq).ker :=
    Abelianization.commutator_subset_ker (originalGalois q hq)
  have hsecond : derivedSeries (originalGroup (p := p) q) 2 ≤
      originalPrincipalUnits q hq := by
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    exact scalar_commutator_mem_principal hn hK q hq x y (hfirst hx) (hfirst hy)
  exact commutator_eq_bot_of_le_principal hK q hq _ hsecond

include hn hK in
/-- Trivial actual Galois image gives a metabelian actual original group. -/
theorem original_derived_two_of_galois_trivial (q : K →ₗ[F] K) (hq : q 1 = 0)
    (hH : (originalGalois (p := p) q hq).range = ⊥) :
    derivedSeries (originalGroup (p := p) q) 2 = ⊥ := by
  have hall (z : originalGroup (p := p) q) : originalGalois q hq z = 1 := by
    have hm : originalGalois q hq z ∈ (originalGalois q hq).range := ⟨z,rfl⟩
    rw [hH] at hm
    exact hm
  have hfirst : derivedSeries (originalGroup (p := p) q) 1 ≤
      originalPrincipalUnits q hq := by
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    exact scalar_commutator_mem_principal hn hK q hq x y (hall x) (hall y)
  exact commutator_eq_bot_of_le_principal hK q hq _ hfirst

#print axioms original_derived_three_eq_bot
#print axioms original_derived_two_of_galois_trivial

include hn hK in
theorem originalConstantScalar_mul (q : K →ₗ[F] K) (hq : q 1 = 0)
    (x y : originalGroup (p := p) q) :
    originalConstantScalar q (x*y) =
      originalConstantScalar q x * originalGalois q hq x (originalConstantScalar q y) := by
  change coefficientZero (x.val.1 (y.val.1 (constantLinear 1))) = _
  rw [original_constant_action hn hK q hq y 1]
  simp only [map_one, mul_one]
  rw [original_constant_action hn hK q hq x]
  simp [coefficientZero, constantLinear]

theorem originalGalois_of_label_one (q : K →ₗ[F] K) (hq : q 1 = 0)
    (z : originalGroup (p := p) q) (hz : z.val.2 = 1) : originalGalois q hq z = 1 := by
  apply AlgEquiv.ext
  intro a
  change originalSigma q hq z a = a
  have h := originalGalois_formula q hq z a
  simpa [originalLabelScalar, hz] using h.symm

end D5.S3.FiniteGroups.GroupAlgebra.OddPrimeJetTop

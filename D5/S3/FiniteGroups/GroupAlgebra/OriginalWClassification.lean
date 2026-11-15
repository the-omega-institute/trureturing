/- GID: D5/S3/FiniteGroups/GroupAlgebra/OriginalWClassification
   generality: E
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/OriginalWClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RepresentationTheory.Intertwining, mathlib/module/Mathlib.Algebra.DirectSum.Module, mathlib/module/Mathlib.LinearAlgebra.TensorPower.Symmetric]
   utility: none
   digest: Transport of the corrected relative tensor criterion to actual dual symmetric powers of a faithful two-dimensional module. -/

import D5.S3.FiniteGroups.GroupAlgebra.EmbeddedOriginalClassification
import D5.S3.FiniteGroups.GroupAlgebra.SymmetricPowerTranslation

/-!
Classical coordinate change and transport for the corrected Elmer--Kadr
Conjecture 3.7 tensor criterion (arXiv:2510.07939v1, Section 2.2).
The arithmetic classification used below is the existing corrected polynomial
classification in EmbeddedOriginalClassification. No novelty or resolution
of the full external problem is claimed.

All three original actions are defined on actual modules: the positive-index
V_i is the dual of Mathlib's quotient SymmetricPower K (Fin (i-1)) W;
M and S are literal direct sums, and T is the actual tensor product.
There is no V_0 in this API. In particular Sym^0 W occurs at V_1, never V_0.
Every M/S summand has a proved positive index. When min u v = 0, S is
literally indexed by Fin 0.

The PHom ideal is precisely the imported RelativeFactors. Its original P
and X witnesses are unrestricted Rep objects. Generator transport retains
the very same P and X, using id_X tensor e and its inverse. Stable errors
are transported by explicit conjugation, not by a new relative relation.

The final theorems consume exists_faithful_polynomial_models, which in turn
consumes the actual two-dimensional normal form; they have no basis,
embedding, symmetric-power-model, or relative-transport premise.

API universe boundary: exact Fin n in the current Mathlib SymmetricPower
forces K : Type. The original RelativeFactors fixes its U,Z,P,X carriers
at the field universe, so the final original W also has W : Type. The
group E has an independent universe. The field need not be finite.

The tensor/direct-sum equivalences and both relative inverse errors below
are constructed explicitly and checked by the native Lean build.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.OriginalWClassification

open D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample
open D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorCounterexample.SymmetricPowerTranslation
open D5.S3.FiniteGroups.GroupAlgebra.EmbeddedOriginalClassification
open D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrResidueCriterion
open Module
open scoped TensorProduct DirectSum

universe uK uG uI uA uB uC uD uM uN uE

section ActualEquivalences

variable {K : Type uK} [Field K] {G : Type uG} [Group G]
  {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D]
  {rho : Representation K G A} {sigma : Representation K G B}
  {tau : Representation K G C} {pi : Representation K G D}

/-- The underlying map is the actual tensor of the two coordinate changes. -/
def tensorCongr (e : rho.Equiv sigma) (f : tau.Equiv pi) :
    (rho.tprod tau).Equiv (sigma.tprod pi) :=
  Representation.Equiv.mk (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv) (by
    intro g
    ext x y
    change e (rho g x) ⊗ₜ[K] f (tau g y) =
      sigma g (e x) ⊗ₜ[K] pi g (f y)
    rw [show e (rho g x) = sigma g (e x) from
      LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) x,
      show f (tau g y) = pi g (f y) from
        LinearMap.congr_fun (f.toIntertwiningMap.isIntertwining' g) y])

end ActualEquivalences

section ActualDirectSums

variable {K : Type uK} [Field K] {G : Type uG} [Group G]
  {I : Type uI} {A : I → Type uA} {B : I → Type uB}
  [∀ i, AddCommGroup (A i)] [∀ i, Module K (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module K (B i)]
  {rho : ∀ i, Representation K G (A i)}
  {sigma : ∀ i, Representation K G (B i)}

/-- Componentwise coordinate change on actual finitely supported direct sums. -/
def directSumCongr (e : ∀ i, (rho i).Equiv (sigma i)) :
    (Representation.directSum rho).Equiv (Representation.directSum sigma) :=
  Representation.Equiv.mk
    (DirectSum.congrLinearEquiv (fun i => (e i).toLinearEquiv)) (by
      intro g
      apply LinearMap.ext
      intro x
      apply DFinsupp.ext
      intro i
      change e i (rho i g (x i)) = sigma i g (e i (x i))
      exact LinearMap.congr_fun ((e i).toIntertwiningMap.isIntertwining' g) (x i))

end ActualDirectSums

section OriginalRelativeTransport

variable {K : Type uK} [Field K] {G : Type uG} [Group G]
  {M : Type uM} {N : Type uN}
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {tau : Representation K G M} {tau' : Representation K G N}

/-- Generator transport keeps the same original Rep witnesses P and X.
The new retract maps are (id_X tensor e) i and r (id_X tensor e)^(-1). -/
theorem relativeProjective_generator_transport
    (e : tau.Equiv tau') (P : Rep.{uK} K G)
    (hP : RelativeProjective tau P) : RelativeProjective tau' P := by
  obtain ⟨X, i, r, hri⟩ := hP
  let t := tensorCongr (Representation.Equiv.refl X.ρ) e
  refine ⟨X, t.toIntertwiningMap.comp i, r.comp t.symm.toIntertwiningMap, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change r (t.symm (t (i x))) = x
  rw [t.symm_apply_apply]
  exact congrArg (fun k => k x) hri

theorem relativeProjective_generator_iff
    (e : tau.Equiv tau') (P : Rep.{uK} K G) :
    RelativeProjective tau P ↔ RelativeProjective tau' P :=
  ⟨relativeProjective_generator_transport e P,
    relativeProjective_generator_transport e.symm P⟩

variable {A B C D : Type uK}
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D]
  {rho : Representation K G A} {rho' : Representation K G B}
  {sigma : Representation K G C} {sigma' : Representation K G D}

/-- Change both endpoints of an actual intertwiner. -/
def transportMap (eA : rho.Equiv rho') (eB : sigma.Equiv sigma')
    (f : rho.IntertwiningMap sigma) : rho'.IntertwiningMap sigma' :=
  eB.toIntertwiningMap.comp (f.comp eA.symm.toIntertwiningMap)

/-- Transport of the ORIGINAL PHom ideal, with the very same factor P
and, through generator transport, the very same unrestricted witness X. -/
theorem relativeFactors_transport
    (eM : tau.Equiv tau') (eA : rho.Equiv rho') (eB : sigma.Equiv sigma')
    {f : rho.IntertwiningMap sigma} (hf : RelativeFactors tau f) :
    RelativeFactors tau' (transportMap eA eB f) := by
  obtain ⟨P, hP, a, b, hba⟩ := hf
  refine ⟨P, (relativeProjective_generator_iff eM P).mp hP,
    a.comp eA.symm.toIntertwiningMap, eB.toIntertwiningMap.comp b, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change eB (b (a (eA.symm x))) = eB (f (eA.symm x))
  exact congrArg eB (congrArg (fun k => k (eA.symm x)) hba)

/-- Explicit conjugation of both inverse errors, retaining the imported
relative ideal. No finite-dimensionality of P or X is used. -/
theorem relativeStableIso_transport
    (eM : tau.Equiv tau') (eA : rho.Equiv rho') (eB : sigma.Equiv sigma')
    (h : RelativeStableIso tau rho sigma) :
    RelativeStableIso tau' rho' sigma' := by
  obtain ⟨f, g, hA, hB⟩ := h
  let f' := transportMap eA eB f
  let g' := transportMap eB eA g
  refine ⟨f', g', ?_, ?_⟩
  · have ht := relativeFactors_transport eM eA eA hA
    have herr : transportMap eA eA (g.comp f - .id rho) =
        g'.comp f' - .id rho' := by
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      change eA (g (f (eA.symm x)) - eA.symm x) =
        eA (g (eB.symm (eB (f (eA.symm x))))) - x
      rw [eB.symm_apply_apply, map_sub, eA.apply_symm_apply]
    rw [herr] at ht
    exact ht
  · have ht := relativeFactors_transport eM eB eB hB
    have herr : transportMap eB eB (f.comp g - .id sigma) =
        f'.comp g' - .id sigma' := by
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      change eB (f (g (eB.symm x)) - eB.symm x) =
        eB (f (eA.symm (eA (g (eB.symm x))))) - x
      rw [eA.symm_apply_apply, map_sub, eB.apply_symm_apply]
    rw [herr] at ht
    exact ht

theorem relativeStableIso_transport_iff
    (eM : tau.Equiv tau') (eA : rho.Equiv rho') (eB : sigma.Equiv sigma') :
    RelativeStableIso tau rho sigma ↔ RelativeStableIso tau' rho' sigma' :=
  ⟨relativeStableIso_transport eM eA eB,
    relativeStableIso_transport eM.symm eA.symm eB.symm⟩

end OriginalRelativeTransport

section OriginalModules

variable (K W : Type) [Field K] [AddCommGroup W] [Module K W]

/-- Positive original index only: this is the ACTUAL quotient symmetric
power, followed by its ordinary linear dual. V_1 is (Sym^0 W)^dual. -/
abbrev OriginalV (i : ℕ) (_hi : 0 < i) :=
  Module.Dual K (SymmetricPower K (Fin (i - 1)) W)

variable {K W}
variable {E : Type uE} [AddCommGroup E]
  (rho : Representation K (Multiplicative E) W)

/-- The actual signed contragredient induced from rho, at a positive index. -/
def originalVAction (i : ℕ) (hi : 0 < i) :
    Representation K (Multiplicative E) (OriginalV K W i hi) :=
  (SymmetricPowerTranslation.action rho (i - 1)).dual

private theorem relative_index_pos (p : ℕ) (hp : 0 < p) (r : ℕ) :
    0 < p * (r + 1) := Nat.mul_pos hp (Nat.succ_pos r)

/-- Positivity of every literal S summand, without a small-degree assumption. -/
theorem expected_index_pos (i j t : ℕ) (hti : t ≤ i) (htj : t ≤ j)
    (ell : Fin t) : 0 < i + j - (2 * ell.val + 1) := by
  have hli : ell.val < i := lt_of_lt_of_le ell.isLt hti
  have hlj : ell.val < j := lt_of_lt_of_le ell.isLt htj
  omega

variable (K W)

/-- The literal original M = direct sum of V_(p(r+1)). -/
abbrev OriginalM (p s : ℕ) (hp : 0 < p) :=
  ⨁ r : Fin s, OriginalV K W (p * (r.val + 1)) (relative_index_pos p hp r.val)

/-- The literal original S. In a zero-residue branch t=0 and the sum is empty. -/
abbrev OriginalS (i j t : ℕ) (hti : t ≤ i) (htj : t ≤ j) :=
  ⨁ ell : Fin t, OriginalV K W (i + j - (2 * ell.val + 1))
    (expected_index_pos i j t hti htj ell)

abbrev OriginalT (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :=
  OriginalV K W i hi ⊗[K] OriginalV K W j hj

variable {K W}

def originalMAction (p s : ℕ) (hp : 0 < p) :
    Representation K (Multiplicative E) (OriginalM K W p s hp) :=
  Representation.directSum (fun r : Fin s =>
    originalVAction rho (p * (r.val + 1)) (relative_index_pos p hp r.val))

def originalSAction (i j t : ℕ) (hti : t ≤ i) (htj : t ≤ j) :
    Representation K (Multiplicative E) (OriginalS K W i j t hti htj) :=
  Representation.directSum (fun ell : Fin t =>
    originalVAction rho (i + j - (2 * ell.val + 1))
      (expected_index_pos i j t hti htj ell))

def originalTAction (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    Representation K (Multiplicative E) (OriginalT K W i j hi hj) :=
  (originalVAction rho i hi).tprod (originalVAction rho j hj)

end OriginalModules

section ConsumedModels

variable {K W : Type} [Field K] [AddCommGroup W] [Module K W]
  {E : Type uE} [AddCommGroup E]
  (rho : Representation K (Multiplicative E) W) (alpha : E →+ K)

/-- Reindex the actual degree-n model only at a proved positive original
index. The degree-zero model is used at i=1, not at i=0. -/
private def positiveDualModel
    (models : ∀ n : ℕ, Nonempty ((SymmetricPowerTranslation.action rho n).dual.Equiv
      ((dualAction K (n + 1)).comp alpha.toMultiplicative)))
    (i : ℕ) (hi : 0 < i) :
    (originalVAction rho i hi).Equiv ((dualAction K i).comp alpha.toMultiplicative) := by
  cases i with
  | zero => omega
  | succ n => simpa [originalVAction, OriginalV] using
      (Classical.choice (models n))

variable
  (eV : ∀ (i : ℕ) (hi : 0 < i),
    (originalVAction rho i hi).Equiv ((dualAction K i).comp alpha.toMultiplicative))

/-- Direct sum of the actual positive-index model equivalences. Restriction
of the polynomial direct sum is definitionally the sum of restrictions. -/
private def originalMEquiv (p s : ℕ) (hp : 0 < p) :
    (originalMAction rho p s hp).Equiv
      ((PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s).comp
        alpha.toMultiplicative) := by
  change (Representation.directSum (fun r : Fin s =>
    originalVAction rho (p * (r.val + 1)) (relative_index_pos p hp r.val))).Equiv
      (Representation.directSum (fun r : Fin s =>
        (dualAction K (p * (r.val + 1))).comp alpha.toMultiplicative))
  exact directSumCongr (fun r => eV _ (relative_index_pos p hp r.val))

private def originalSEquiv (i j t : ℕ) (hti : t ≤ i) (htj : t ≤ j) :
    (originalSAction rho i j t hti htj).Equiv
      ((expectedAction (K := K) i j t).comp alpha.toMultiplicative) := by
  change (Representation.directSum (fun ell : Fin t =>
    originalVAction rho (i + j - (2 * ell.val + 1))
      (expected_index_pos i j t hti htj ell))).Equiv
      (Representation.directSum (fun ell : Fin t =>
        (dualAction K (i + j - (2 * ell.val + 1))).comp alpha.toMultiplicative))
  exact directSumCongr (fun ell => eV _ (expected_index_pos i j t hti htj ell))

private def originalTEquiv (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    (originalTAction rho i j hi hj).Equiv
      ((ElmerKadrResidueCriterion.tensorAction (K := K) i j).comp
        alpha.toMultiplicative) := by
  change ((originalVAction rho i hi).tprod (originalVAction rho j hj)).Equiv
    (Representation.tprod ((dualAction K i).comp alpha.toMultiplicative)
      ((dualAction K j).comp alpha.toMultiplicative))
  exact tensorCongr (eV i hi) (eV j hj)

end ConsumedModels

section FaithfulOriginalW

variable {K W : Type} [Field K] [AddCommGroup W] [Module K W]
  {E : Type uE} [AddCommGroup E] [Nontrivial E]
  {p : ℕ} [Fact p.Prime] [CharP K p] [FiniteDimensional K W]

/-- One injective alpha transports all literal original modules at once.
The actual normal form and actual quotient symmetric-power theorem discharge
every coordinate premise. The left side is entirely alpha-free. -/
theorem exists_originalW_transport
    (hE : ∀ e : E, p • e = 0) (hdim : finrank K W = 2)
    (rho : Representation K (Multiplicative E) W) (hrho : Function.Injective rho) :
    ∃ alpha : E →+ K, Function.Injective alpha ∧
      ∀ (s i j t : ℕ) (hi : 0 < i) (hj : 0 < j) (hti : t ≤ i) (htj : t ≤ j),
        RelativeStableIso
          (originalMAction rho p s (Fact.out : p.Prime).pos)
          (originalSAction rho i j t hti htj)
          (originalTAction rho i j hi hj) ↔
        RelativeStableIso
          ((PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s).comp
            alpha.toMultiplicative)
          ((expectedAction (K := K) i j t).comp alpha.toMultiplicative)
          ((ElmerKadrResidueCriterion.tensorAction (K := K) i j).comp
            alpha.toMultiplicative) := by
  obtain ⟨alpha, halpha, _primalModels, dualModels⟩ :=
    SymmetricPowerTranslation.exists_faithful_polynomial_models hE hdim rho hrho
  let eV := positiveDualModel rho alpha dualModels
  refine ⟨alpha, halpha, ?_⟩
  intro s i j t hi hj hti htj
  exact relativeStableIso_transport_iff
    (originalMEquiv rho alpha eV p s (Fact.out : p.Prime).pos)
    (originalSEquiv rho alpha eV i j t hti htj)
    (originalTEquiv rho alpha eV i j hi hj)

private theorem min_residue_le_left (p a u v : ℕ) : min u v ≤ p * a + u := by
  have := min_le_left u v
  omega

private theorem min_residue_le_right (p b u v : ℕ) : min u v ≤ p * b + v := by
  have := min_le_right u v
  omega

variable [Fintype E]

/-- Corrected binomial classification for the ACTUAL original W modules.
M is sum_(r<q/p) V_(p(r+1)); S is sum_(ell<min u v) V_(i+j-(2ell+1));
T is V_i tensor V_j. The original PHom definition, including all original
Rep P and X witnesses, is unchanged. No field-finiteness premise is used.

The external positive-index assumptions are retained. Separate i<q and j<q
are unnecessary: they follow here from i,j>0 and i+j<=q. -/
theorem originalW_relative_criterion
    (hE : ∀ e : E, p • e = 0) (hdim : finrank K W = 2)
    (rho : Representation K (Multiplicative E) W) (hrho : Function.Injective rho)
    (a b u v : ℕ)
    (hi : 0 < p * a + u) (hj : 0 < p * b + v)
    (hup : u < p) (hvp : v < p) (huv : u + v ≤ p)
    (hsize : (p * a + u) + (p * b + v) ≤ Fintype.card E) :
    RelativeStableIso
      (originalMAction rho p (Fintype.card E / p) (Fact.out : p.Prime).pos)
      (originalSAction rho (p * a + u) (p * b + v) (min u v)
        (min_residue_le_left p a u v) (min_residue_le_right p b u v))
      (originalTAction rho (p * a + u) (p * b + v) hi hj) ↔
      u = 0 ∨ v = 0 ∨ ((a + b).choose a : K) ≠ 0 := by
  obtain ⟨alpha, halpha, htransport⟩ := exists_originalW_transport hE hdim rho hrho
  exact (htransport (Fintype.card E / p) (p * a + u) (p * b + v) (min u v)
    hi hj (min_residue_le_left p a u v) (min_residue_le_right p b u v)).trans
    (original_relative_criterion_for_embedding alpha halpha a b u v hup hvp huv hsize)

/-- The complete Kummer no-carry form of the same original-W criterion.
All high-digit carries are tested; the two zero-residue branches remain. -/
theorem originalW_relative_criterion_no_carry
    (hE : ∀ e : E, p • e = 0) (hdim : finrank K W = 2)
    (rho : Representation K (Multiplicative E) W) (hrho : Function.Injective rho)
    (a b u v : ℕ)
    (hi : 0 < p * a + u) (hj : 0 < p * b + v)
    (hup : u < p) (hvp : v < p) (huv : u + v ≤ p)
    (hsize : (p * a + u) + (p * b + v) ≤ Fintype.card E) :
    RelativeStableIso
      (originalMAction rho p (Fintype.card E / p) (Fact.out : p.Prime).pos)
      (originalSAction rho (p * a + u) (p * b + v) (min u v)
        (min_residue_le_left p a u v) (min_residue_le_right p b u v))
      (originalTAction rho (p * a + u) (p * b + v) hi hj) ↔
      u = 0 ∨ v = 0 ∨ ∀ k ∈ Finset.Ico 1 (Nat.log p (a + b) + 1),
        a % p ^ k + b % p ^ k < p ^ k := by
  obtain ⟨alpha, halpha, htransport⟩ := exists_originalW_transport hE hdim rho hrho
  exact (htransport (Fintype.card E / p) (p * a + u) (p * b + v) (min u v)
    hi hj (min_residue_le_left p a u v) (min_residue_le_right p b u v)).trans
    (original_relative_criterion_no_carry alpha halpha a b u v hup hvp huv hsize)

end FaithfulOriginalW

end D5.S3.FiniteGroups.GroupAlgebra.OriginalWClassification

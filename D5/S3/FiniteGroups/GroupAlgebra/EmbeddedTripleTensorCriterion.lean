/- GID: D5/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion
   generality: E
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/EmbeddedTripleTensorCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Trace]
   utility: none
   digest: Exact high-digit criterion for the literal original-relative triple tensor sum. -/

import D5.S3.FiniteGroups.GroupAlgebra.EmbeddedTripleTensorObstruction
import D5.S3.FiniteGroups.GroupAlgebra.ElmerKadrTensorReflection
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Exact criterion for the literal triple tensor sum

The displayed dependent direct sum contains its top polynomial dual as an actual
equivariant retract. The unrestricted original relative factorization of a stable
inverse error survives this retract. Its trace vanishes by the relative trace theorem,
whereas the all-map triple obstruction forces the inverse composite to have zero trace.
Lucas factorization and the nonzero top dimension give the necessary high-digit condition.
Conversely, two actual binary decompositions distribute and flatten to the literal
dependent triple sum. Their complement remains relatively projective through explicit
tensor and direct-sum retractions, giving the sufficient direction in the original ideal.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.FiniteGroups.GroupAlgebra.EmbeddedTripleTensorCriterion

open ElmerKadrTensorCounterexample EmbeddedOriginalClassification
open scoped TensorProduct DirectSum

universe uK uE

variable {K : Type uK} [Field K]

/-- The two actual Clebsch--Gordan indices, with the second range depending on the first. -/
abbrev TripleIndex (u v w : ℕ) :=
  (ell : Fin (min u v)) × Fin (min (u + v - 2 * ell.val - 1) w)

def summandDimension (i j k : ℕ) {u v w : ℕ} (z : TripleIndex u v w) : ℕ :=
  i + j + k - 2 * z.1.val - 2 * z.2.val - 2

/-- The literal displayed dependent direct sum of original polynomial duals. -/
abbrev ExpectedSpace (i j k u v w : ℕ) :=
  ⨁ z : TripleIndex u v w, DualPower K (summandDimension i j k z)

def expectedAction (i j k u v w : ℕ) :
    Representation K (Multiplicative K) (ExpectedSpace (K := K) i j k u v w) :=
  Representation.directSum (fun z : TripleIndex u v w =>
    dualAction K (summandDimension i j k z))

/-- The actual left-parenthesized triple tensor, with the original module dimensions. -/
def tensorAction (i j k : ℕ) :
    Representation K (Multiplicative K)
      ((DualPower K i ⊗[K] DualPower K j) ⊗[K] DualPower K k) :=
  ((dualAction K i).tprod (dualAction K j)).tprod (dualAction K k)

def topIndex (u v w : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w) :
    TripleIndex u v w :=
  ⟨⟨0, by omega⟩, ⟨0, by simp only [mul_zero, Nat.sub_zero]; omega⟩⟩

section Retract

variable {E : Type uE} [AddCommGroup E] (α : E →+ K)

/-- Inclusion of the literal ell=h=0 summand, after restriction along alpha. -/
def topInclusion (i j k u v w : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w) :
    Representation.IntertwiningMap ((dualAction K (i + j + k - 2)).comp α.toMultiplicative)
      ((expectedAction i j k u v w).comp α.toMultiplicative) where
  toLinearMap := DirectSum.lof K (TripleIndex u v w)
    (fun z => DualPower K (summandDimension i j k z)) (topIndex u v w hu hv hw)
  isIntertwining' e := by
    apply LinearMap.ext
    intro x
    exact (DirectSum.lmap_lof
      (fun z : TripleIndex u v w => dualAction K (summandDimension i j k z)
        (α.toMultiplicative e)) (topIndex u v w hu hv hw) x).symm

/-- Projection onto the same literal top summand. -/
def topProjection (i j k u v w : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w) :
    Representation.IntertwiningMap ((expectedAction i j k u v w).comp α.toMultiplicative)
      ((dualAction K (i + j + k - 2)).comp α.toMultiplicative) where
  toLinearMap := DirectSum.component K (TripleIndex u v w)
    (fun z => DualPower K (summandDimension i j k z)) (topIndex u v w hu hv hw)
  isIntertwining' e := by
    apply LinearMap.ext
    intro x
    rfl

theorem topProjection_inclusion (i j k u v w : ℕ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w) :
    (topProjection α i j k u v w hu hv hw).comp (topInclusion α i j k u v w hu hv hw) =
      .id ((dualAction K (i + j + k - 2)).comp α.toMultiplicative) := by
  classical
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact DirectSum.component.lof_self (R := K) (ι := TripleIndex u v w)
    (M := fun z => DualPower K (summandDimension i j k z)) (topIndex u v w hu hv hw) x

end Retract

section Arithmetic

variable {p : ℕ} [Fact p.Prime] [CharP K p]

theorem degree_binomial_product (a b c u v w : ℕ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w) (hsum : u + v + w ≤ p + 1) :
    ((((p * a + u) + (p * b + v) - 2).choose (p * a + u - 1) : K) *
      (((p * a + u) + (p * b + v) + (p * c + w) - 3).choose
        ((p * a + u) + (p * b + v) - 2) : K)) =
      (((u - 1 + (v - 1)).choose (u - 1) : K) *
        ((u - 1 + (v - 1) + (w - 1)).choose (u - 1 + (v - 1)) : K)) *
        (((a + b).choose a : K) * ((a + b + c).choose (a + b) : K)) := by
  have hfirst : (((p * a + u) + (p * b + v) - 2).choose (p * a + u - 1) : K) =
      ((u - 1 + (v - 1)).choose (u - 1) : K) * ((a + b).choose a : K) := by
    rw [show (p * a + u) + (p * b + v) - 2 =
        (p * a + (u - 1)) + (p * b + (v - 1)) by omega,
      show p * a + u - 1 = p * a + (u - 1) by omega]
    exact ElmerKadrResidueCriterion.choose_low_digits a b (u - 1) (v - 1) (by omega)
  have hsecond :
      (((p * a + u) + (p * b + v) + (p * c + w) - 3).choose
        ((p * a + u) + (p * b + v) - 2) : K) =
      ((u - 1 + (v - 1) + (w - 1)).choose (u - 1 + (v - 1)) : K) *
        ((a + b + c).choose (a + b) : K) := by
    rw [show (p * a + u) + (p * b + v) + (p * c + w) - 3 =
        (p * (a + b) + (u - 1 + (v - 1))) + (p * c + (w - 1)) by
          rw [Nat.mul_add]; omega,
      show (p * a + u) + (p * b + v) - 2 =
        p * (a + b) + (u - 1 + (v - 1)) by rw [Nat.mul_add]; omega]
    exact ElmerKadrResidueCriterion.choose_low_digits (a + b) c
      (u - 1 + (v - 1)) (w - 1) (by omega)
  rw [hfirst, hsecond]
  ring

omit [Fact p.Prime] in
theorem top_dimension_ne_zero (a b c u v w : ℕ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w) (hsum : u + v + w ≤ p + 1) :
    (((p * a + u) + (p * b + v) + (p * c + w) - 2 : ℕ) : K) ≠ 0 := by
  have hsum' : (p * a + u) + (p * b + v) + (p * c + w) =
      p * (a + b + c) + (u + v + w) := by ring
  have hdim : (p * a + u) + (p * b + v) + (p * c + w) - 2 =
      p * (a + b + c) + (u + v + w - 2) := by rw [hsum']; omega
  rw [hdim, Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero K p, zero_mul, zero_add]
  intro hz
  have hd : p ∣ u + v + w - 2 := (CharP.cast_eq_zero_iff K p _).mp hz
  have hp_le := Nat.le_of_dvd (by omega : 0 < u + v + w - 2) hd
  omega

end Arithmetic

section TraceObstruction

variable {E : Type uE} [AddCommGroup E] [Fintype E]
variable (α : E →+ K) (hα : Function.Injective α)

include hα

/-- The accepted all-map obstruction, expressed in original positive module dimensions. -/
theorem trace_zero_of_degree_product_zero (i j k : ℕ)
    (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) (hsize : i + j + k ≤ Fintype.card E + 1)
    (hchoose : ((i + j - 2).choose (i - 1) : K) *
      ((i + j + k - 3).choose (i + j - 2) : K) = 0)
    (f : Representation.IntertwiningMap
      ((dualAction K (i + j + k - 2)).comp α.toMultiplicative)
      ((tensorAction i j k).comp α.toMultiplicative))
    (g : Representation.IntertwiningMap ((tensorAction i j k).comp α.toMultiplicative)
      ((dualAction K (i + j + k - 2)).comp α.toMultiplicative)) :
    LinearMap.trace K (DualPower K (i + j + k - 2))
      (g.toLinearMap.comp f.toLinearMap) = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hD : (n + 1) + (m + 1) + (r + 1) - 2 = n + m + r + 1 := by omega
  have hL : (n + 1) + (m + 1) - 2 = n + m := by omega
  have hN : (n + 1) + (m + 1) + (r + 1) - 3 = n + m + r := by omega
  revert f g
  rw [hD]
  intro f g
  rw [hL, hN, show n.succ - 1 = n by omega] at hchoose
  exact EmbeddedTripleTensorObstruction.embedded_composition_trace_zero α hα n m r
    (by omega) hchoose f g

end TraceObstruction

section NecessaryCondition

variable {p : ℕ} [Fact p.Prime] [CharP K p]
variable {E : Type uE} [AddCommGroup E] [Fintype E]

/-- Necessary high-digit condition for the displayed literal sum and the existing original
relative ideal. Its projective and tensor witnesses remain unrestricted. -/
theorem original_relative_necessary_for_embedding
    (α : E →+ K) (hα : Function.Injective α)
    (a b c u v w : ℕ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w) (hsum : u + v + w ≤ p + 1)
    (hsize : (p * a + u) + (p * b + v) + (p * c + w) ≤ Fintype.card E + 1)
    (hs : RelativeStableIso
      ((PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)
        (Fintype.card E / p)).comp α.toMultiplicative)
      ((expectedAction (p * a + u) (p * b + v) (p * c + w) u v w).comp α.toMultiplicative)
      ((tensorAction (p * a + u) (p * b + v) (p * c + w)).comp α.toMultiplicative)) :
    ((a + b).choose a : K) * ((a + b + c).choose (a + b) : K) ≠ 0 := by
  intro hzero
  let i := p * a + u
  let j := p * b + v
  let k := p * c + w
  have hi : 0 < i := by dsimp [i]; omega
  have hj : 0 < j := by dsimp [j]; omega
  have hk : 0 < k := by dsimp [k]; omega
  change i + j + k ≤ Fintype.card E + 1 at hsize
  have hcard : 1 < Fintype.card E := by omega
  obtain ⟨e, he⟩ := Fintype.exists_ne_of_one_lt_card hcard (0 : E)
  have hchoose : ((i + j - 2).choose (i - 1) : K) *
      ((i + j + k - 3).choose (i + j - 2) : K) = 0 := by
    rw [show ((i + j - 2).choose (i - 1) : K) *
        ((i + j + k - 3).choose (i + j - 2) : K) = _ from
      degree_binomial_product a b c u v w hu hv hw hsum]
    rw [hzero, mul_zero]
  have hdim : ((i + j + k - 2 : ℕ) : K) ≠ 0 :=
    top_dimension_ne_zero a b c u v w hu hv hw hsum
  let τ := (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)
    (Fintype.card E / p)).comp α.toMultiplicative
  let jU := topInclusion α i j k u v w hu hv hw
  let pU := topProjection α i j k u v w hu hv hw
  have hpj : pU.comp jU = .id ((dualAction K (i + j + k - 2)).comp α.toMultiplicative) :=
    topProjection_inclusion α i j k u v w hu hv hw
  obtain ⟨f, g, hS, _⟩ := hs
  let fU := f.comp jU
  let gU := pU.comp g
  have herror : RelativeFactors τ
      (gU.comp fU - .id ((dualAction K (i + j + k - 2)).comp α.toMultiplicative)) := by
    obtain ⟨P, hP, β, γ, hγβ⟩ := hS
    refine ⟨P, hP, β.comp jU, pU.comp γ, ?_⟩
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change pU (γ (β (jU x))) = pU (g (f (jU x))) - x
    have hx := congrArg (fun q => q (jU x)) hγβ
    change γ (β (jU x)) = g (f (jU x)) - jU x at hx
    have hpx := congrArg (fun q => q x) hpj
    change pU (jU x) = x at hpx
    rw [hx, map_sub, hpx]
  let : Module.Finite K (DualPower K (i + j + k - 2)) :=
    Module.Finite.of_basis (dualBasis K (i + j + k - 2))
  have hid : LinearMap.trace K (DualPower K (i + j + k - 2)) LinearMap.id =
      ((i + j + k - 2 : ℕ) : K) := by
    rw [LinearMap.trace_id, Module.finrank_eq_card_basis (dualBasis K (i + j + k - 2))]
    simp
  have htrace := trace_relativeFactors_for_embedding (p := p) α hα e he
    (Fintype.card E / p) _ _ herror
  have htensor := trace_zero_of_degree_product_zero α hα i j k hi hj hk hsize hchoose fU gU
  change LinearMap.trace K (DualPower K (i + j + k - 2))
    (gU.toLinearMap.comp fU.toLinearMap - LinearMap.id) = 0 at htrace
  rw [map_sub, htensor, hid] at htrace
  exact hdim (neg_eq_zero.mp (by simpa only [zero_sub] using htrace))

end NecessaryCondition

section ActualDecompositionOperations

variable {G A B C D M : Type uK} [Group G]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D]
  [AddCommGroup M] [Module K M]

private theorem projective_tensor (τ : Representation K G M)
    (ρ : Representation K G A) (σ : Representation K G B)
    (hρ : RelativeProjective τ (Rep.of ρ)) :
    RelativeProjective τ (Rep.of (ρ.tprod σ)) := by
  obtain ⟨X, i, r, hri⟩ := hρ
  let e := (Representation.TensorProduct.assoc X.ρ τ σ).trans
    ((ElmerKadrTensorReflection.tensorCongr (Representation.Equiv.refl X.ρ)
      (Representation.TensorProduct.comm τ σ)).trans
      (Representation.TensorProduct.assoc X.ρ σ τ).symm)
  refine ⟨Rep.of (X.ρ.tprod σ),
    e.toIntertwiningMap.comp (i.rTensor σ),
    (r.rTensor σ).comp e.symm.toIntertwiningMap, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change (r.rTensor σ) (e.symm (e ((i x) ⊗ₜ[K] y))) = x ⊗ₜ[K] y
  rw [e.symm_apply_apply]
  change r (i x) ⊗ₜ[K] y = x ⊗ₜ[K] y
  rw [show r (i x) = x from congrArg (fun q => q x) hri]

end ActualDecompositionOperations

section ActualSums

variable {G : Type uK} [Group G] {I : Type} {A B : I → Type uK}
  [∀ i, AddCommGroup (A i)] [∀ i, Module K (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module K (B i)]

private def sumIntertwiner {ρ : ∀ i, Representation K G (A i)}
    {σ : ∀ i, Representation K G (B i)} (f : ∀ i, (ρ i).IntertwiningMap (σ i)) :
    (Representation.directSum ρ).IntertwiningMap (Representation.directSum σ) where
  toLinearMap := DirectSum.lmap (fun i => (f i).toLinearMap)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro i
    exact LinearMap.congr_fun ((f i).isIntertwining' g) (x i)

private def sumEquiv {ρ : ∀ i, Representation K G (A i)}
    {σ : ∀ i, Representation K G (B i)} (e : ∀ i, (ρ i).Equiv (σ i)) :
    (Representation.directSum ρ).Equiv (Representation.directSum σ) :=
  .mk (DirectSum.congrLinearEquiv (fun i => (e i).toLinearEquiv))
    (sumIntertwiner (fun i => (e i).toIntertwiningMap)).isIntertwining'

private def tensorSum {C : Type uK} [AddCommGroup C] [Module K C]
    (ρ : ∀ i, Representation K G (A i)) (σ : Representation K G C) :
    ((Representation.directSum ρ).tprod σ).Equiv
      (Representation.directSum (fun i => (ρ i).tprod σ)) := by
  classical
  refine .mk (TensorProduct.directSumLeft K K A C) ?_
  intro g
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply DFinsupp.ext
  intro i
  change (TensorProduct.directSumLeft K K A C)
      (((Representation.directSum ρ) g x) ⊗ₜ[K] (σ g y)) i =
    TensorProduct.map ((ρ i) g) (σ g)
      ((TensorProduct.directSumLeft K K A C) (x ⊗ₜ[K] y) i)
  simp only [TensorProduct.directSumLeft_tmul, Representation.directSum_apply,
    DirectSum.lmap_apply, TensorProduct.map_tmul]

private def sumProd [Fintype I]
    (ρ : ∀ i, Representation K G (A i)) (σ : ∀ i, Representation K G (B i)) :
    (Representation.directSum (fun i => (ρ i).prod (σ i))).Equiv
      ((Representation.directSum ρ).prod (Representation.directSum σ)) := by
  let f : (∀ i, A i × B i) ≃ₗ[K] (∀ i, A i) × (∀ i, B i) :=
    { toFun := fun x => (fun i => (x i).1, fun i => (x i).2)
      invFun := fun x i => (x.1 i, x.2 i)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine .mk ((DirectSum.linearEquivFunOnFintype K I (fun i => A i × B i)).trans
    (f.trans ((DirectSum.linearEquivFunOnFintype K I A).symm.prodCongr
      (DirectSum.linearEquivFunOnFintype K I B).symm))) ?_
  intro g
  apply LinearMap.ext
  intro x
  apply Prod.ext <;> apply DFinsupp.ext <;> intro i <;> rfl

private def flattenSum {J : I → Type} {C : (i : I) → J i → Type uK}
    [∀ i j, AddCommGroup (C i j)] [∀ i j, Module K (C i j)]
    (ρ : ∀ i j, Representation K G (C i j)) :
    (Representation.directSum (fun i => Representation.directSum (ρ i))).Equiv
      (Representation.directSum (fun z : Sigma J => ρ z.1 z.2)) := by
  classical
  refine .mk (DirectSum.sigmaLcurryEquiv K).symm ?_
  intro g
  apply LinearMap.ext
  intro x
  apply DFinsupp.ext
  intro z
  rfl

private theorem projective_sum {M : Type uK}
    [AddCommGroup M] [Module K M] (τ : Representation K G M)
    (ρ : ∀ i, Representation K G (A i))
    (hρ : ∀ i, RelativeProjective τ (Rep.of (ρ i))) :
    RelativeProjective τ (Rep.of (Representation.directSum ρ)) := by
  classical
  choose X inc ret hret using hρ
  let e := tensorSum (fun i => (X i).ρ) τ
  refine ⟨Rep.of (Representation.directSum (fun i => (X i).ρ)),
    e.symm.toIntertwiningMap.comp (sumIntertwiner inc),
    (sumIntertwiner ret).comp e.toIntertwiningMap, ?_⟩
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change (sumIntertwiner ret) (e (e.symm ((sumIntertwiner inc) x))) = x
  rw [e.apply_symm_apply]
  apply DFinsupp.ext
  intro i
  exact congrArg (fun q => q (x i)) (hret i)

end ActualSums

section SufficientDecomposition

variable {p : ℕ} [Fact p.Prime] [CharP K p]

/-- Iterating the actual binary splittings gives the literal dependent triple sum
and an actual original relative-projective complement. -/
theorem triple_decomposition (s a b c u v w : ℕ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w) (hsum : u + v + w ≤ p + 1)
    (hab : a + b ≤ s) (hc : c ≤ s)
    (hchoose : ((a + b).choose a : K) * ((a + b + c).choose (a + b) : K) ≠ 0) :
    ∃ P : Rep.{uK} K (Multiplicative K),
      RelativeProjective (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s) P ∧
      Nonempty ((tensorAction (p * a + u) (p * b + v) (p * c + w)).Equiv
        ((expectedAction (p * a + u) (p * b + v) (p * c + w) u v w).prod P.ρ)) := by
  classical
  have h₁ := (mul_ne_zero_iff.mp hchoose).1
  have h₂ := (mul_ne_zero_iff.mp hchoose).2
  let i := p * a + u
  let j := p * b + v
  let k := p * c + w
  let r (ell : Fin (min u v)) := u + v - 2 * ell.val - 1
  have hru (ell : Fin (min u v)) : ell.val < u :=
    lt_of_lt_of_le ell.isLt (min_le_left u v)
  have hrv (ell : Fin (min u v)) : ell.val < v :=
    lt_of_lt_of_le ell.isLt (min_le_right u v)
  have hr (ell : Fin (min u v)) : 1 ≤ r ell := by
    dsimp [r]
    have := hru ell
    have := hrv ell
    omega
  have hrw (ell : Fin (min u v)) : r ell + w ≤ p := by
    dsimp [r]
    have := hru ell
    have := hrv ell
    omega
  have hd (ell : Fin (min u v)) :
      i + j - (2 * ell.val + 1) = p * (a + b) + r ell := by
    dsimp [i, j, r]
    rw [Nat.mul_add]
    have := hru ell
    have := hrv ell
    omega
  let Lρ (ell : Fin (min u v)) := dualAction K (p * (a + b) + r ell)
  let Cρ := dualAction K k
  let R₁ := ElmerKadrResidueCriterion.tensorAction (K := K)
    (i - min u v) (j - min u v)
  let S₂ (ell : Fin (min u v)) := ElmerKadrResidueCriterion.expectedAction (K := K)
    (p * (a + b) + r ell) k (min (r ell) w)
  let R₂ (ell : Fin (min u v)) := ElmerKadrResidueCriterion.tensorAction (K := K)
    (p * (a + b) + r ell - min (r ell) w) (k - min (r ell) w)
  let Pρ := (Representation.directSum R₂).prod (R₁.tprod Cρ)
  have hR₁ : RelativeProjective
      (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s) (Rep.of R₁) :=
    ElmerKadrResidueCriterion.residue_remainder_relativeProjective s a b u v
      (by omega) (by omega)
  have hR₂ : ∀ ell, RelativeProjective
      (PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p) s) (Rep.of (R₂ ell)) :=
    fun ell => ElmerKadrResidueCriterion.residue_remainder_relativeProjective
      s (a + b) c (r ell) w hab hc
  refine ⟨Rep.of Pρ, ElmerKadrTensorReflection.projective_prod _
    (ρ := Representation.directSum R₂) (σ := R₁.tprod Cρ)
    (projective_sum _ R₂ hR₂) (projective_tensor _ R₁ Cρ hR₁), ?_⟩
  obtain ⟨e₁⟩ := ElmerKadrResidueCriterion.residue_decomposition (K := K)
    a b u v hu hv (by omega) h₁
  let eL := ElmerKadrResidueCriterion.directSumCongr (K := K)
    (fun ell : Fin (min u v) => i + j - (2 * ell.val + 1))
    (fun ell => p * (a + b) + r ell) (funext hd)
  let e₂ (ell : Fin (min u v)) : ((Lρ ell).tprod Cρ).Equiv
      ((S₂ ell).prod (R₂ ell)) :=
    Classical.choice (ElmerKadrResidueCriterion.residue_decomposition (K := K)
      (a + b) c (r ell) w (hr ell) hw (hrw ell) h₂)
  let eS := (tensorSum Lρ Cρ).trans ((sumEquiv e₂).trans (sumProd S₂ R₂))
  let d (z : TripleIndex u v w) :=
    (p * (a + b) + r z.1) + k - (2 * z.2.val + 1)
  have hdim : d = fun z : TripleIndex u v w => summandDimension i j k z := by
    funext z
    have h₀ := hd z.1
    have h₁ := hru z.1
    have h₂ := hrv z.1
    have hi : u ≤ i := by dsimp [i]; omega
    have hj : v ≤ j := by dsimp [j]; omega
    dsimp [d, summandDimension]
    omega
  let eF := (flattenSum (fun ell (h : Fin (min (r ell) w)) =>
    dualAction K ((p * (a + b) + r ell) + k - (2 * h.val + 1)))).trans
      (ElmerKadrResidueCriterion.directSumCongr (K := K) d (fun z => summandDimension i j k z) hdim)
  exact ⟨(ElmerKadrTensorReflection.tensorCongr
    (e₁.trans (ElmerKadrResidueCriterion.prodCongr eL (Representation.Equiv.refl R₁)))
    (Representation.Equiv.refl Cρ)).trans
      ((ElmerKadrTensorReflection.tensorProdLeft (Representation.directSum Lρ) R₁ Cρ).trans
        ((ElmerKadrResidueCriterion.prodCongr eS (Representation.Equiv.refl _)).trans
          ((ElmerKadrResidueCriterion.prodCongr
            (ElmerKadrResidueCriterion.prodCongr eF (Representation.Equiv.refl _))
            (Representation.Equiv.refl _)).trans
            (ElmerKadrResidueCriterion.prodAssoc (expectedAction i j k u v w) (Representation.directSum R₂)
              (R₁.tprod Cρ)))))⟩

end SufficientDecomposition

section RestrictStableMaps

variable {G : Type uK} [Group G] {H : Type uE} [Group H]
  {A B M : Type uK} [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B] [AddCommGroup M] [Module K M]

/-- Restriction retains the original, unrestricted projective and tensor witnesses. -/
private theorem restrict_stable (ι : H →* G) (τ : Representation K G M)
    (ρ : Representation K G A) (σ : Representation K G B)
    (h : RelativeStableIso τ ρ σ) :
    RelativeStableIso (τ.comp ι) (ρ.comp ι) (σ.comp ι) := by
  have factors {V W : Type uK} [AddCommGroup V] [Module K V]
      [AddCommGroup W] [Module K W]
      {υ : Representation K G V} {ω : Representation K G W}
      (q : υ.IntertwiningMap ω) (hq : RelativeFactors τ q) :
      RelativeFactors (τ.comp ι) (restrictIntertwiner ι q) := by
    obtain ⟨P, hP, a, b, hba⟩ := hq
    refine ⟨Rep.of (P.ρ.comp ι), restrict_relativeProjective ι τ hP,
      restrictIntertwiner ι a, restrictIntertwiner ι b, ?_⟩
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun q => q x) hba
  obtain ⟨f, g, hgf, hfg⟩ := h
  exact ⟨restrictIntertwiner ι f, restrictIntertwiner ι g,
    factors _ hgf, factors _ hfg⟩

end RestrictStableMaps

section CompleteCriterion

variable {p : ℕ} [Fact p.Prime] [CharP K p]
variable {E : Type uE} [AddCommGroup E] [Fintype E]

/-- Sufficiency for the literal displayed triple sum and the original relative ideal. -/
theorem original_relative_sufficient_for_embedding
    (α : E →+ K) (hα : Function.Injective α)
    (a b c u v w : ℕ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w) (hsum : u + v + w ≤ p + 1)
    (hsize : (p * a + u) + (p * b + v) + (p * c + w) ≤ Fintype.card E + 1)
    (hchoose : ((a + b).choose a : K) * ((a + b + c).choose (a + b) : K) ≠ 0) :
    RelativeStableIso
      ((PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)
        (Fintype.card E / p)).comp α.toMultiplicative)
      ((expectedAction (p * a + u) (p * b + v) (p * c + w) u v w).comp α.toMultiplicative)
      ((tensorAction (p * a + u) (p * b + v) (p * c + w)).comp α.toMultiplicative) := by
  have hcard : 1 < Fintype.card E := by omega
  let : Nontrivial E := Fintype.one_lt_card_iff_nontrivial.mp hcard
  have htop := top_relative_dimension (p := p) α hα
  let s := Fintype.card E / p
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hbound : a + b + c ≤ s := by
    by_contra h
    have ht : s + 1 ≤ a + b + c := by omega
    have hm := Nat.mul_le_mul_left p ht
    dsimp [s] at hm ⊢
    simp only [Nat.mul_add, Nat.mul_one, htop] at hm
    nlinarith
  obtain ⟨P, hP, ⟨e⟩⟩ := triple_decomposition (K := K) s a b c u v w
    hu hv hw hsum (by omega) (by omega) hchoose
  exact restrict_stable α.toMultiplicative _ _ _
    (ElmerKadrResidueCriterion.relativeStableIso_of_decomposition _ _ _ P.ρ e hP)

/-- Complete three-factor criterion for the literal dependent direct sum, with
the original relative-projective ideal and no finite-field assumption. -/
theorem original_relative_iff_for_embedding
    (α : E →+ K) (hα : Function.Injective α)
    (a b c u v w : ℕ)
    (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w) (hsum : u + v + w ≤ p + 1)
    (hsize : (p * a + u) + (p * b + v) + (p * c + w) ≤ Fintype.card E + 1) :
    RelativeStableIso
      ((PrimeCyclicRelativeTrace.relativeAction (K := K) (p := p)
        (Fintype.card E / p)).comp α.toMultiplicative)
      ((expectedAction (p * a + u) (p * b + v) (p * c + w) u v w).comp α.toMultiplicative)
      ((tensorAction (p * a + u) (p * b + v) (p * c + w)).comp α.toMultiplicative) ↔
    ((a + b).choose a : K) * ((a + b + c).choose (a + b) : K) ≠ 0 :=
  ⟨original_relative_necessary_for_embedding α hα a b c u v w hu hv hw hsum hsize,
    original_relative_sufficient_for_embedding α hα a b c u v w hu hv hw hsum hsize⟩

end CompleteCriterion

end D5.S3.FiniteGroups.GroupAlgebra.EmbeddedTripleTensorCriterion

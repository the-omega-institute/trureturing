/- GID: D5/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Modules/FullJacobiZhuTopRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The genuine Zhu quotient acts on Top with a finite joint current decomposition. -//- Delivery scope and attribution: 35 of the original 39 authored entries are retained, including both local quotient instances. The unconsumed Top-to-positive-current wrapper and finite representative wrapper, together with the newly dead positive-current intersection definition and zeroMode_finite helper, are retired under CLAUDE.md 3.2; their exact formulas, hypotheses and derivations remain mathematical consequences documented in the owning Scribe narrative and verified by transient exact compiled checks. No consumer is added for bookkeeping. proof_shape: content in homogeneous-zero stability and the genuine unital full Q-to-End(Top) construction; the mixed-Jacobi residue transports and computational helpers are bind-only and consumed on their live proof paths. admission_basis: escape-witness. utility: none: symbolic constructions for arbitrary original lattice data and an independent-universe arbitrary complex module, including rank zero and zero Top, rather than bounded enumeration or certified instances. Source Gram positivity is exactly hD/hPos. Top uses every homogeneous original source state at every integer degree and all modes at least that degree. The finite source Node/Grid action is ON Top; AllAlpha survival retains its nonzero premise. No target grading, nonzero/generation/faithfulness/ambient finiteness or equality with the positive-current vacuum is assumed. Original supplier attribution remains below. The source-bound four-slot audit remains unfinished under https://github.com/the-omega-institute/trureturing/issues/29518: the original 25 public-theorem targets now have 22 retained and 3 retired entries. No declared_validated status, client enrollment or Contract registration is claimed. The original full VOA/CFT/anomaly/fusion/string/AdS goal remains active and incomplete. -/
/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the repository root LICENSE.
Source-faithful adaptation of the Zhu residue construction in
Fedor-Popov/Lean_VOA, revision 013a799ca834a8a6b3afa8129e3e522025b3f45c,
VOA/Modules/ZhuModule.lean and VOA/Modules/ZeroModeMult.lean.
The finite residue argument is Zhu's module construction; the native
generic residue lemmas and original source quotient retain their attribution.
The full mixed-Jacobi supplier retains its Scott Carnahan / Kalle Kytölä attribution.

Native elaboration and axiom evidence are recorded separately from this source.
No publication or official acceptance is asserted by this file.

The new step is the connection to an arbitrary full mixed-Jacobi module M.
Top means annihilation by ALL source states at ALL indices at least their
integer source degree. Commutator and actual source degree prove stability.
The positive-current vacuum is only a proved upper bound for Top.
No target grading, nonzero top, finite dimension, basis, faithful action,
semisimplicity, generation, or equality with that current vacuum is assumed.
All source states, charges, gradings, cocycles and integer indices are original.
-/

import D5.S3.VertexAlgebra.Modules.FullJacobiCurrentTransport
import D5.S3.VertexAlgebra.Lattice.NormFourZhuAlgebra.Core
import D5.S3.VertexAlgebra.Lattice.ActualZhuSourceProjectors

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeSugawaraConformal LatticeSugawaraCurrents LatticePositiveEnergy
open FullJacobiCurrentTransport
open Lattice.ActualZhuProduct
open LatticeHalfFockGroundRightCurrentTransport.Calculus
open scoped BigOperators VertexOperator DirectSum

noncomputable section
universe u
variable {D : LatticeData} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The actual Zhu top: every integer source degree and every high mode.
This is a subspace of M, not a selected sector or a Heisenberg substitute. -/
def Top (J : FullJacobiLatticeModule D M) : Submodule ℂ M where
  carrier := {w | ∀ (h n : ℤ) (a : Carrier D), a ∈ grade D h → h ≤ n →
    mode J a n w = 0}
  zero_mem' := by
    intro h n a ha hn
    exact map_zero (mode J a n)
  add_mem' := by
    intro v w hv hw h n a ha hn
    rw [map_add, hv h n a ha hn, hw h n a ha hn, add_zero]
  smul_mem' := by
    intro c w hw h n a ha hn
    rw [map_smul, hw h n a ha hn, smul_zero]

/-- Identify the adapter's current with the existing actual source current. -/
theorem currentState_eq_actual (i : Fin D.rank) :
    FullJacobiCurrentTransport.currentState D i =
      LatticeActualConformalState.currentState D i :=
  LatticeActualConformalState.current_state_creation D i

theorem currentState_mem_grade (i : Fin D.rank) :
    FullJacobiCurrentTransport.currentState D i ∈ grade D 1 := by
  rw [currentState_eq_actual]
  exact Lattice.ActualZhuGroundCurrent.current_grade D i

/-- A homogeneous zero mode preserves the genuine top. The source fused
state has degree k+h-i-1, whereas its module mode is n+h-1-i. Their
difference is n-k, so every commutator term kills the original Top vector. -/
theorem homogeneous_zero_preserves_top (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (h : ℤ) (a : Carrier D) (ha : a ∈ grade D h)
    (w : M) (hw : w ∈ Top J) :
    mode J a (h - 1) w ∈ Top J := by
  classical
  intro k n b hb hn
  have term_zero (i : ℕ) : commutatorTerm J b a n (h - 1) i w = 0 := by
    have hg : sourceProduct D b i a ∈ grade D (k + h - (i : ℤ) - 1) :=
      positive_actual_mode_grade D hD k h i b a hb ha
    have hz := hw (k + h - (i : ℤ) - 1) (n + (h - 1) - i)
      (sourceProduct D b i a) hg (by omega)
    simpa only [commutatorTerm, LinearMap.smul_apply, hz, smul_zero]
  have sum_zero : (∑ᶠ i : ℕ, commutatorTerm J b a n (h - 1) i) w = 0 := by
    change (LinearMap.applyₗ w) (∑ᶠ i : ℕ, commutatorTerm J b a n (h - 1) i) = 0
    rw [map_finsum (LinearMap.applyₗ w) (commutator_terms_finite J b a n (h - 1))]
    simpa only [LinearMap.applyₗ_apply_apply, term_zero, finsum_zero]
  have hc := congrArg (fun A : Module.End ℂ M => A w)
    (module_mode_commutator J b a n (h - 1))
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at hc
  rw [hw k n b hb hn, map_zero, sub_zero, sum_zero] at hc
  exact hc

/-- Full arbitrary-M Jacobi in the already existing residue calculus.
All three finite supports are transported separately before splitting a sum. -/
theorem module_fullLaw (J : FullJacobiLatticeModule D M) (a b : Carrier D) :
    fullLaw (J.stateField a) (J.stateField b)
      (fun r => J.stateField (sourceProduct D a r b)) 0 := by
  have binom (p : ℤ) (i : ℕ) :
      StateFieldResidueReconstruction.integerBinomial p i = Ring.choose (p : ℂ) i :=
    Ring.map_choose (Int.castRingHom ℂ) p i
  intro p q r w
  obtain ⟨hl, hf, hs, h⟩ := J.borcherds a b w p q r
  have el : jacobiLeft J.stateField a b w p q r =
      leftTerm (fun t => J.stateField (sourceProduct D a t b)) 0 p q r w := by
    funext i
    simp [jacobiLeft, leftTerm, binom]
  have ef : jacobiFirst J.stateField a b w p q r =
      firstTerm (J.stateField a) (J.stateField b) p q r w := by
    funext i
    simp [jacobiFirst, firstTerm, LatticeHalfFockGroundRightCurrentTransport.residueWeight,
      binom]
  have es : jacobiSecond J.stateField a b w p q r =
      secondTerm (J.stateField a) (J.stateField b) p q r w := by
    funext i
    simp [jacobiSecond, secondTerm, LatticeHalfFockGroundRightCurrentTransport.residueWeight,
      StateFieldResidueReconstruction.epsilon, binom]
  refine ⟨el ▸ hl, ef ▸ hf, es ▸ hs, ?_⟩
  simp_rw [smul_sub] at h
  change (∑ᶠ i : ℕ, jacobiLeft J.stateField a b w p q r i) =
    ∑ᶠ i : ℕ, (jacobiFirst J.stateField a b w p q r i -
      jacobiSecond J.stateField a b w p q r i) at h
  rw [finsum_sub_distrib hf hs, el, ef, es] at h
  exact h

private def homogeneousZero (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ) :
    grade D h →ₗ[ℂ] Module.End ℂ (Top J) := by
  let z (a : grade D h) : Module.End ℂ (Top J) := {
    toFun w := ⟨mode J a.val (h - 1) w.val,
      homogeneous_zero_preserves_top J hD h a.val a.property w.val w.property⟩
    map_add' v w := Subtype.ext ((mode J a.val (h - 1)).map_add v.val w.val)
    map_smul' c w := Subtype.ext ((mode J a.val (h - 1)).map_smul c w.val) }
  refine { toFun := z, map_add' := ?_, map_smul' := ?_ }
  · intro a b
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change mode J (a.val + b.val) (h - 1) w.val = _
    simp [z, mode]
  · intro c a
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change mode J (c • a.val) (h - 1) w.val = _
    simp [z, mode]

/-- Source-linear raw zero mode on every original, possibly mixed-energy,
state. Linearity uses the actual internal direct sum, not an arbitrary
choice of a homogeneous presentation or a target grading. -/
def zeroMode (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    Carrier D →ₗ[ℂ] Module.End ℂ (Top J) :=
  (DirectSum.toModule ℂ ℤ (Module.End ℂ (Top J)) (homogeneousZero J hD)).comp
    (carrierEnergyDecomposition D).toLinearMap

/-- Evaluation includes every integer degree, including negative fused degrees. -/
theorem zeroMode_homogeneous (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (h : ℤ) (a : Carrier D) (ha : a ∈ grade D h) (w : Top J) :
    (zeroMode J hD a w).val = mode J a (h - 1) w.val := by
  have he : carrierEnergyDecomposition D a =
      DirectSum.lof ℂ ℤ (fun n => grade D n) h ⟨a, ha⟩ := by
    apply (carrierEnergyDecomposition D).symm.injective
    simp [carrierEnergyDecomposition]
  change (DirectSum.toModule ℂ ℤ (Module.End ℂ (Top J)) _
    (carrierEnergyDecomposition D a) w).val = _
  rw [he, DirectSum.toModule_lof]
  rfl

private theorem circle_homogeneous (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (p q : ℕ) (a b : Carrier D)
    (ha : a ∈ grade D (p : ℤ)) (hb : b ∈ grade D (q : ℤ)) :
    zeroMode J hD (Lattice.NormFourZhuFinite.circle D p a b) = 0 := by
  classical
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  have he (j : ℕ) :
      (zeroMode J hD (mu D a ((j : ℤ) - 2) b) w).val =
        mode J (mu D a ((j : ℤ) - 2) b) ((p : ℤ) + q - j) w.val := by
    have hg := positive_actual_mode_grade D hD (p : ℤ) (q : ℤ) ((j : ℤ) - 2)
      a b ha hb
    have hi : ((p : ℤ) + q - ((j : ℤ) - 2) - 1) - 1 = (p : ℤ) + q - j := by omega
    simpa only [hi, mu] using zeroMode_homogeneous J hD _ _ hg w
  change (zeroMode J hD
    (∑ j ∈ Finset.range (p + 1), (p.choose j : ℂ) • mu D a ((j : ℤ) - 2) b) w).val = 0
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_smul]
  simp_rw [he]
  have hz := Lattice.NormFourZhuAlgebra.Core.circle_residue_top
    (J.stateField a) (J.stateField b) (fun r => J.stateField (sourceProduct D a r b))
    (module_fullLaw J a b) p q w.val
    (fun j => w.property _ _ a ha (by omega))
    (fun j => w.property _ _ b hb (by omega))
  simpa only [mode, sourceProduct, mu,
    show ∀ j : ℕ, -2 + (j : ℤ) = (j : ℤ) - 2 from fun j => by omega] using hz

private theorem star_homogeneous_zeroMode (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (p q : ℕ) (a b : Carrier D)
    (ha : a ∈ grade D (p : ℤ)) (hb : b ∈ grade D (q : ℤ)) :
    zeroMode J hD (star D a b) = zeroMode J hD a * zeroMode J hD b := by
  classical
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  have he (j : ℕ) :
      (zeroMode J hD (mu D a ((j : ℤ) - 1) b) w).val =
        mode J (mu D a ((j : ℤ) - 1) b) ((p : ℤ) + q - 1 - j) w.val := by
    have hg := positive_actual_mode_grade D hD (p : ℤ) (q : ℤ) ((j : ℤ) - 1)
      a b ha hb
    have hi : ((p : ℤ) + q - ((j : ℤ) - 1) - 1) - 1 = (p : ℤ) + q - 1 - j := by omega
    simpa only [hi, mu] using zeroMode_homogeneous J hD _ _ hg w
  rw [star_homogeneous D p a b ha]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_smul, Module.End.mul_apply]
  simp_rw [he, zeroMode_homogeneous J hD _ a ha, zeroMode_homogeneous J hD _ b hb]
  have hz := Lattice.NormFourZhuAlgebra.Core.star_residue_top
    (J.stateField a) (J.stateField b) (fun r => J.stateField (sourceProduct D a r b))
    (module_fullLaw J a b) p q w.val
    (fun j => w.property _ _ a ha (by omega))
    (fun j => w.property _ _ b hb (by omega))
  simpa only [mode, sourceProduct, mu,
    show ∀ j : ℕ, -1 + (j : ℤ) = (j : ℤ) - 1 from fun j => by omega,
    show ∀ j : ℕ, (p : ℤ) + ((q : ℤ) - 1) - j = (p : ℤ) + q - 1 - j
      from fun j => by omega] using hz

/-- Every literal circle generator acts by zero; its second state is unrestricted. -/
theorem zeroMode_circle (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (p : ℕ) (a b : Carrier D) (ha : a ∈ grade D (p : ℤ)) :
    zeroMode J hD (Lattice.NormFourZhuFinite.circle D p a b) = 0 := by
  classical
  have hb := sum_gradeProjections D b
  have he : Lattice.NormFourZhuFinite.circle D p a b =
      ∑ q ∈ stateEnergies D b,
        Lattice.NormFourZhuFinite.circle D p a (gradeProjection D q b) := by
    conv_lhs => rw [← hb]
    simp only [Lattice.NormFourZhuFinite.circle, mu, map_sum, Finset.smul_sum]
    exact Finset.sum_comm
  rw [he, map_sum]
  apply Finset.sum_eq_zero
  intro q hq
  have hqn : (q.toNat : ℤ) = q :=
    Int.toNat_of_nonneg (stateEnergies_nonneg hD b q hq)
  exact circle_homogeneous J hD p q.toNat a (gradeProjection D q b) ha
    (by simpa only [hqn] using gradeProjection_mem D q b)

/-- The entire original O-space is killed, rather than a finite proxy or sector O-space. -/
theorem zhuO_le_kernel (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    Lattice.ActualZhuFinite.zhuO D ≤ LinearMap.ker (zeroMode J hD) := by
  apply Submodule.span_le.mpr
  rintro z ⟨p, a, b, ha, rfl⟩
  exact zeroMode_circle J hD p a b ha

/-- Multiplicativity on BOTH arbitrary original mixed-energy arguments. -/
theorem zeroMode_star (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a b : Carrier D) :
    zeroMode J hD (star D a b) = zeroMode J hD a * zeroMode J hD b := by
  classical
  have he : star D a b = ∑ p ∈ stateEnergies D a, ∑ q ∈ stateEnergies D b,
      star D (gradeProjection D p a) (gradeProjection D q b) := by
    conv_lhs => rw [← sum_gradeProjections D a, ← sum_gradeProjections D b]
    simp only [map_sum, LinearMap.sum_apply]
    exact Finset.sum_comm
  rw [he, map_sum]
  have hm (p : ℤ) (hp : p ∈ stateEnergies D a) (q : ℤ) (hq : q ∈ stateEnergies D b) :
      zeroMode J hD (star D (gradeProjection D p a) (gradeProjection D q b)) =
        zeroMode J hD (gradeProjection D p a) * zeroMode J hD (gradeProjection D q b) := by
    have hpn : (p.toNat : ℤ) = p := Int.toNat_of_nonneg (stateEnergies_nonneg hD a p hp)
    have hqn : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (stateEnergies_nonneg hD b q hq)
    exact star_homogeneous_zeroMode J hD p.toNat q.toNat _ _
      (by simpa only [hpn] using gradeProjection_mem D p a)
      (by simpa only [hqn] using gradeProjection_mem D q b)
  simp_rw [map_sum]
  calc
    _ = ∑ p ∈ stateEnergies D a, ∑ q ∈ stateEnergies D b,
        zeroMode J hD (gradeProjection D p a) * zeroMode J hD (gradeProjection D q b) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact Finset.sum_congr rfl (fun q hq => hm p hp q hq)
    _ = _ := by
      rw [← Finset.sum_mul_sum, ← map_sum, ← map_sum,
        sum_gradeProjections, sum_gradeProjections]

theorem zeroMode_vacuum (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    zeroMode J hD (vacuum D) = 1 := by
  have hv : vacuum D ∈ grade D 0 := by
    rw [grade_zero D hD]
    exact Submodule.subset_span (Set.mem_singleton _)
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  rw [zeroMode_homogeneous J hD 0 _ hv, vacuum_modes]
  simp

/-- Descent to the EXISTING literal Q and its EXISTING ring/algebra structures. -/
def representation (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    letI := Lattice.ActualZhuAlgebra.quotientRing D hD
    letI := Lattice.ActualZhuAlgebra.quotientAlgebra D hD
    Lattice.ActualZhuAlgebra.Q D →ₐ[ℂ] Module.End ℂ (Top J) := by
  letI := Lattice.ActualZhuAlgebra.quotientRing D hD
  letI := Lattice.ActualZhuAlgebra.quotientAlgebra D hD
  let f := (Lattice.ActualZhuFinite.zhuO D).liftQ (zeroMode J hD) (zhuO_le_kernel J hD)
  apply AlgHom.ofLinearMap f
  · exact zeroMode_vacuum J hD
  · intro x y
    obtain ⟨a, rfl⟩ := (Lattice.ActualZhuFinite.zhuO D).mkQ_surjective x
    obtain ⟨b, rfl⟩ := (Lattice.ActualZhuFinite.zhuO D).mkQ_surjective y
    change f (Lattice.ActualZhuAlgebra.quotientProduct D hD _ _) = _
    rw [Lattice.ActualZhuAlgebra.quotientProduct_mk]
    exact zeroMode_star J hD a b

/-- Homogeneous representative computation with the original mode convention. -/
theorem representation_mk (J : FullJacobiLatticeModule D M)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (h : ℤ) (a : Carrier D) (ha : a ∈ grade D h) (w : Top J) :
    (representation J hD ((Lattice.ActualZhuFinite.zhuO D).mkQ a) w).val =
      mode J a (h - 1) w.val :=
  zeroMode_homogeneous J hD h a ha w

section Spectrum

variable (J : FullJacobiLatticeModule D M)
variable [hPos : Fact (Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))]
local instance : Ring (Lattice.ActualZhuAlgebra.Q D) :=
  Lattice.ActualZhuAlgebra.quotientRing D hPos.out
local instance : Algebra ℂ (Lattice.ActualZhuAlgebra.Q D) :=
  Lattice.ActualZhuAlgebra.quotientAlgebra D hPos.out

open Lattice.ActualZhuCurrentNormalForm Lattice.ActualZhuSourceProjectors
open Lattice.ActualZhuMinimum

/-- Current mode zero restricted to Top using the proved homogeneous stability. -/
def currentZero (i : Fin D.rank) : Module.End ℂ (Top J) :=
  homogeneousZero J hPos.out 1
    ⟨FullJacobiCurrentTransport.currentState D i, currentState_mem_grade i⟩

theorem currentZero_apply (i : Fin D.rank) (w : Top J) :
    (currentZero J i w).val = current J i 0 w.val := rfl

/-- The existing actual Zhu current H acts as the actual arbitrary-module J_i(0). -/
theorem representation_H (i : Fin D.rank) :
    representation J hPos.out (H D i) = currentZero J i := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  rw [currentZero_apply]
  change (representation J hPos.out ((Lattice.ActualZhuFinite.zhuO D).mkQ
    (LatticeActualConformalState.currentState D i)) w).val = _
  rw [representation_mk J hPos.out 1 _ (Lattice.ActualZhuGroundCurrent.current_grade D i)]
  rw [← currentState_eq_actual]
  rfl

/-- Restriction of the genuine quotient action, consumed by the source projectors. -/
def currentRepresentation : currentAlgebra D →ₐ[ℂ] Module.End ℂ (Top J) :=
  (representation J hPos.out).comp (currentAlgebra D).val

theorem currentRepresentation_generator (i : Fin D.rank) :
    currentRepresentation J (currentGenerator D i) = currentZero J i :=
  representation_H J i

def coordinateProjectorAction (i : Fin D.rank) (j : Node D i) : Module.End ℂ (Top J) :=
  currentRepresentation J (coordinateProjector D i j)

theorem coordinateProjectorAction_sum (i : Fin D.rank) :
    ∑ j : Node D i, coordinateProjectorAction J i j = 1 := by
  classical
  have he := congrArg (currentRepresentation J) (coordinate_sum D i)
  simpa only [map_sum, map_one, coordinateProjectorAction] using he

theorem coordinateProjectorAction_eigen (i : Fin D.rank) (j : Node D i) :
    currentZero J i * coordinateProjectorAction J i j =
      (node D i j : ℂ) • coordinateProjectorAction J i j := by
  have he := congrArg (currentRepresentation J) (coordinate_eigen D i j)
  simpa only [map_mul, map_smul, currentRepresentation_generator,
    coordinateProjectorAction] using he

/-- A finite coordinate resolution of the actual restricted current. -/
theorem currentZero_coordinate_resolution (i : Fin D.rank) :
    currentZero J i = ∑ j : Node D i,
      (node D i j : ℂ) • coordinateProjectorAction J i j := by
  classical
  calc
    currentZero J i = currentZero J i * (∑ j : Node D i, coordinateProjectorAction J i j) := by
      rw [coordinateProjectorAction_sum, mul_one]
    _ = _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => coordinateProjectorAction_eigen J i j)

def projectorAction (r : Grid D) : Module.End ℂ (Top J) :=
  currentRepresentation J (projector D r)

theorem projectorAction_sum : ∑ r : Grid D, projectorAction J r = 1 := by
  classical
  have he := congrArg (currentRepresentation J) (projector_sum D)
  simpa only [map_sum, map_one, projectorAction] using he

theorem projectorAction_eigen (r : Grid D) (i : Fin D.rank) :
    currentZero J i * projectorAction J r =
      (gridWeight D r i : ℂ) • projectorAction J r := by
  have he := congrArg (currentRepresentation J) (projector_eigen D r i)
  simpa only [map_mul, map_smul, currentRepresentation_generator, projectorAction] using he

/-- Only NONZERO images force source survival. Zero source projectors and
zero action images are allowed, and no faithful action is used. -/
theorem projectorAction_survives (r : Grid D) (hr : projectorAction J r ≠ 0) :
    AllAlpha D (gridWeight D r) := by
  apply projector_survives D r
  intro hz
  apply hr
  simp only [projectorAction, hz, map_zero]

/-- Joint current eigenspaces inside Top, with no dimension restriction. -/
def jointEigenspace (r : Grid D) : Submodule ℂ (Top J) :=
  ⨅ i : Fin D.rank, (currentZero J i).eigenspace (gridWeight D r i : ℂ)

theorem projectorAction_mem_joint (r : Grid D) (w : Top J) :
    projectorAction J r w ∈ jointEigenspace J r := by
  simp only [jointEigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  intro i
  have he := congrArg (fun A : Module.End ℂ (Top J) => A w) (projectorAction_eigen J r i)
  simpa only [Module.End.mul_apply, LinearMap.smul_apply] using he

theorem sum_projectorAction (w : Top J) : ∑ r : Grid D, projectorAction J r w = w := by
  classical
  have he := congrArg (fun A : Module.End ℂ (Top J) => A w) (projectorAction_sum J)
  simpa only [LinearMap.sum_apply, Module.End.one_apply] using he

/-- Every arbitrary Top vector is a finite sum of joint eigencomponents.
Each nonzero component has a surviving all-alpha weight. The finite index
set exists also in rank zero; no component or image is required nonzero. -/
theorem finite_joint_current_decomposition (w : Top J) :
    ∃ v : Grid D → Top J,
      (∑ r : Grid D, v r) = w ∧
      (∀ r, v r ∈ jointEigenspace J r) ∧
      (∀ r (i : Fin D.rank),
        current J i 0 (v r).val = (gridWeight D r i : ℂ) • (v r).val) ∧
      (∀ r, v r ≠ 0 → AllAlpha D (gridWeight D r)) ∧
      (∀ i : Fin D.rank, current J i 0 w.val = ∑ j : Node D i,
        (node D i j : ℂ) • (coordinateProjectorAction J i j w).val) := by
  classical
  refine ⟨fun r => projectorAction J r w, sum_projectorAction J w,
    fun r => projectorAction_mem_joint J r w, ?_, ?_, ?_⟩
  · intro r i
    have he := congrArg (fun A : Module.End ℂ (Top J) => (A w).val)
      (projectorAction_eigen J r i)
    simpa only [Module.End.mul_apply, currentZero_apply, LinearMap.smul_apply,
      Submodule.coe_smul] using he
  · intro r hr
    apply projectorAction_survives J r
    intro hz
    apply hr
    change projectorAction J r w = 0
    rw [hz, LinearMap.zero_apply]
  · intro i
    have he := congrArg (fun A : Module.End ℂ (Top J) => (A w).val)
      (currentZero_coordinate_resolution J i)
    simpa only [currentZero_apply, LinearMap.sum_apply, Submodule.coe_sum,
      LinearMap.smul_apply, Submodule.coe_smul] using he

end Spectrum
end
end D5.S3.VertexAlgebra.Modules.FullJacobiZhuTopRepresentation

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality
import D5.S3.FiniteGroups.FiniteCharacterAlgebra
import Reg.D5.S3.Quantum.Analysis.CompactGroups.UnitaryRepresentationKernel
import Reg.Support.DependentFamily
import Reg.Support.RealScalarLift

/-! Source-bound audits of the Schur orthogonality relations for matrix coefficients of
continuous irreducible representations of a compact group. The parameters of each readout are
read through accessor functions. -/

namespace Reg.D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality

open MeasureTheory
open _root_.D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.Analysis.CompactGroups.UnitaryRepresentationKernel
  (Two twoTop twoDiscrete twoTopGroup twoCompact)

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe t u v w

/-! ## A two-element model -/

/-- The sign of an element of the two-element group, as an integer. -/
def signInt : Two.{u} →* ℤ where
  toFun g := if g = 1 then 1 else -1
  map_one' := by decide
  map_mul' := by decide

/-- The non-identity element of the two-element group. -/
def flip : Two.{u} := ⟨Multiplicative.ofAdd 1⟩

theorem flip_ne_one : flip.{u} ≠ 1 := by decide

/-- The sign representation of the two-element group on a vector space over a field. -/
def signRep (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V] :
    Representation K Two.{u} V :=
  (algebraMap K (Module.End K V)).toMonoidHom.comp
    ((Int.castRingHom K).toMonoidHom.comp signInt.{u})

theorem signRep_flip (K : Type*) [Field K] {V : Type*} [AddCommGroup V] [Module K V] (x : V) :
    signRep.{u} K V flip x = -x := by
  simp [signRep, signInt, flip_ne_one]

/-- Over a field in which `2 ≠ 0`, the sign representation on a nonzero space is not equivalent
to a trivial representation. -/
theorem signRep_not_equiv_trivial (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) (V W : Type*)
    [AddCommGroup V] [Module K V] [Nontrivial V] [AddCommGroup W] [Module K W] :
    IsEmpty ((signRep.{u} K V).Equiv (Representation.trivial K Two.{u} W)) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have h := LinearMap.congr_fun (e.isIntertwining' flip.{u}) x
  simp only [LinearMap.comp_apply, Representation.trivial_apply] at h
  rw [signRep_flip, map_neg] at h
  have h2x : (2 : K) • e.toLinearMap x = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h]
    exact neg_add_cancel _
  have h1 : e.toLinearEquiv x = 0 := (smul_eq_zero.1 h2x).resolve_left h2
  exact hx (e.toLinearEquiv.injective (h1.trans (map_zero _).symm))

/-- On a compact discrete group, every Haar measure gives the identity a positive finite mass. -/
theorem integral_indicator_one_ne_zero {𝕜 : Type*} [RCLike 𝕜] {G : Type*} [Group G]
    [TopologicalSpace G] [DiscreteTopology G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] :
    ∫ g, Set.indicator {(1 : G)} (1 : G → 𝕜) g ∂μ ≠ 0 := by
  rw [integral_indicator (measurableSet_singleton 1), Pi.one_def, setIntegral_const]
  have h0 : μ {(1 : G)} ≠ 0 := (isOpen_discrete _).measure_ne_zero μ (Set.singleton_nonempty 1)
  have ht : μ {(1 : G)} ≠ ⊤ := measure_ne_top μ _
  have : μ.real {(1 : G)} ≠ 0 := by
    rw [measureReal_def]
    exact (ENNReal.toReal_pos h0 ht).ne'
  exact smul_ne_zero this one_ne_zero

/-! ### The complex line -/

/-- The complex line in universe `v`. -/
abbrev Line := ULift.{v} ℂ

theorem finrank_line : Module.finrank ℂ Line.{v} = 1 :=
  ULift.moduleEquiv.finrank_eq.trans (Module.finrank_self ℂ)

theorem line_finiteDimensional : FiniteDimensional ℂ Line.{v} :=
  Module.Finite.equiv ULift.moduleEquiv.symm

/-- The sign representation of the two-element group on the complex line. -/
abbrev sign : Representation ℂ Two.{u} Line.{v} := signRep ℂ Line.{v}

theorem trivial_irreducible : (Representation.trivial ℂ Two.{u} Line.{v}).IsIrreducible :=
  _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation.isIrreducible_of_finrank_eq_one
    _ finrank_line

/-- The coordinate functional of the complex line. -/
def coord : Module.Dual ℂ Line.{v} := ULift.moduleEquiv.toLinearMap

/-! ### The real line over the real numbers lifted to universe `t` -/

/-- The real numbers in universe `t`, with the shared `RCLike` structure. -/
abbrev LiftReal := ULift.{t} ℝ

/-- The real line in universe `v`, a normed space over `LiftReal`. -/
abbrev RLine := ULift.{v} ℝ

/-- The real line is linearly equivalent to its scalar field. -/
def rlineEquiv : RLine.{v} ≃ₗ[LiftReal.{t}] LiftReal.{t} :=
  LinearEquiv.ofLinearMap Reg.Support.RealScalarLift.lineIsometry.{t, v, t}.toLinearMap
    Reg.Support.RealScalarLift.lineIsometry.{t, t, v}.toLinearMap
    (LinearMap.ext fun _ => rfl) (LinearMap.ext fun _ => rfl)

theorem finrank_rline : Module.finrank LiftReal.{t} RLine.{v} = 1 :=
  (rlineEquiv : RLine.{v} ≃ₗ[LiftReal.{t}] LiftReal.{t}).finrank_eq.trans
    (Module.finrank_self LiftReal.{t})

theorem rline_finiteDimensional : FiniteDimensional LiftReal.{t} RLine.{v} :=
  Module.Finite.equiv (rlineEquiv : RLine.{v} ≃ₗ[LiftReal.{t}] LiftReal.{t}).symm

theorem two_ne_zero_liftReal : (2 : LiftReal.{t}) ≠ 0 := by
  intro h
  have := congrArg ULift.down h
  norm_num at this

/-- The coordinate functional of the real line. -/
def coordR : Module.Dual LiftReal.{t} RLine.{v} :=
  (rlineEquiv : RLine.{v} ≃ₗ[LiftReal.{t}] LiftReal.{t}).toLinearMap

theorem coordR_one : coordR.{t, v} (1 : RLine.{v}) = 1 := rfl

theorem signR_irreducible : (signRep.{u} LiftReal.{t} RLine.{v}).IsIrreducible :=
  _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation.isIrreducible_of_finrank_eq_one
    _ finrank_rline

theorem trivialR_irreducible :
    (Representation.trivial LiftReal.{t} Two.{u} RLine.{w}).IsIrreducible :=
  _root_.D5.S3.FiniteGroups.FiniteCharacterAlgebra.TauCeti.Representation.isIrreducible_of_finrank_eq_one
    _ finrank_rline

/-! ## Inequivalent representations: the coefficient `g ↦ φ (ρ g v)` over `𝕜` -/
namespace CoefficientField

set_option linter.checkUnivs false in
/-- The data of the matrix coefficient `g ↦ φ (ρ g v)` of a representation on a normed space
over a field with the `RCLike` structure. -/
abbrev Params : Type (max (t + 1) (u + 1) (v + 1)) :=
  Σ K : Type t, Σ G : Type u, Σ V : Type v, Σ _ : RCLike K, Σ _ : Group G,
    Σ _ : NormedAddCommGroup V, Σ _ : NormedSpace K V, Σ _ : Representation K G V,
      Σ _ : Module.Dual K V, V

/-- The scalar field of a coefficient datum. -/
@[reducible] def scalars (p : Params.{t, u, v}) : Type t := p.1

/-- The group of a coefficient datum. -/
@[reducible] def carrier (p : Params.{t, u, v}) : Type u := p.2.1

/-- The space of a coefficient datum. -/
@[reducible] def space (p : Params.{t, u, v}) : Type v := p.2.2.1

/-- The data of a coefficient datum after its types. -/
def rest₁ (p : Params.{t, u, v}) : Σ iK : RCLike (scalars p), Σ iG : Group (carrier p),
    Σ iV : NormedAddCommGroup (space p), Σ iS : (letI := iK; letI := iV;
      NormedSpace (scalars p) (space p)),
    Σ _ : (letI := iK; letI := iG; letI := iV; letI := iS;
      Representation (scalars p) (carrier p) (space p)),
    Σ _ : (letI := iK; letI := iV; letI := iS; Module.Dual (scalars p) (space p)), space p :=
  p.2.2.2

/-- The `RCLike` structure of the scalar field of a coefficient datum. -/
@[reducible] def rclike (p : Params.{t, u, v}) : RCLike (scalars p) := (rest₁ p).1

/-- The data of a coefficient datum after its scalar structure. -/
def rest₂ (p : Params.{t, u, v}) : Σ iG : Group (carrier p),
    Σ iV : NormedAddCommGroup (space p), Σ iS : (letI := rclike p; letI := iV;
      NormedSpace (scalars p) (space p)),
    Σ _ : (letI := rclike p; letI := iG; letI := iV; letI := iS;
      Representation (scalars p) (carrier p) (space p)),
    Σ _ : (letI := rclike p; letI := iV; letI := iS; Module.Dual (scalars p) (space p)),
      space p :=
  (rest₁ p).2

/-- The group structure of a coefficient datum. -/
@[reducible] def group (p : Params.{t, u, v}) : Group (carrier p) := (rest₂ p).1

/-- The data of a coefficient datum after its group structure. -/
def rest₃ (p : Params.{t, u, v}) : Σ iV : NormedAddCommGroup (space p),
    Σ iS : (letI := rclike p; letI := iV; NormedSpace (scalars p) (space p)),
    Σ _ : (letI := rclike p; letI := group p; letI := iV; letI := iS;
      Representation (scalars p) (carrier p) (space p)),
    Σ _ : (letI := rclike p; letI := iV; letI := iS; Module.Dual (scalars p) (space p)),
      space p :=
  (rest₂ p).2

/-- The norm of the space of a coefficient datum. -/
@[reducible] def normed (p : Params.{t, u, v}) : NormedAddCommGroup (space p) := (rest₃ p).1

/-- The data of a coefficient datum after its norm. -/
def rest₄ (p : Params.{t, u, v}) :
    Σ iS : (letI := rclike p; letI := normed p; NormedSpace (scalars p) (space p)),
    Σ _ : (letI := rclike p; letI := group p; letI := normed p; letI := iS;
      Representation (scalars p) (carrier p) (space p)),
    Σ _ : (letI := rclike p; letI := normed p; letI := iS; Module.Dual (scalars p) (space p)),
      space p :=
  (rest₃ p).2

/-- The normed space structure of a coefficient datum. -/
@[reducible] def normedSpace (p : Params.{t, u, v}) :
    letI := rclike p; letI := normed p; NormedSpace (scalars p) (space p) := (rest₄ p).1

/-- The data of a coefficient datum after its normed space structure. -/
def rest₅ (p : Params.{t, u, v}) :
    Σ _ : (letI := rclike p; letI := group p; letI := normed p; letI := normedSpace p;
      Representation (scalars p) (carrier p) (space p)),
    Σ _ : (letI := rclike p; letI := normed p; letI := normedSpace p;
      Module.Dual (scalars p) (space p)), space p :=
  (rest₄ p).2

/-- The representation of a coefficient datum. -/
def rep (p : Params.{t, u, v}) :
    letI := rclike p; letI := group p; letI := normed p; letI := normedSpace p
    Representation (scalars p) (carrier p) (space p) := (rest₅ p).1

/-- The functional and the vector of a coefficient datum. -/
def rest₆ (p : Params.{t, u, v}) :
    Σ _ : (letI := rclike p; letI := normed p; letI := normedSpace p;
      Module.Dual (scalars p) (space p)), space p :=
  (rest₅ p).2

/-- The functional of a coefficient datum. -/
def dual (p : Params.{t, u, v}) :
    letI := rclike p; letI := normed p; letI := normedSpace p
    Module.Dual (scalars p) (space p) := (rest₆ p).1

/-- The vector of a coefficient datum. -/
def vec (p : Params.{t, u, v}) : space p := (rest₆ p).2

set_option linter.checkUnivs false in
/-- The matrix coefficient `g ↦ φ (ρ g v)`, with values in the scalar field. -/
abbrev signature : Signature where
  Params := Params.{t, u, v}
  State p := carrier p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := scalars p
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{t, u, v} :=
  realize signature (fun _ p g => letI := rclike p; letI := group p; letI := normed p;
    letI := normedSpace p; dual p (rep p g (vec p))) (fun e => nomatch e)

/-- The indicator of the identity element, read in place of every coefficient. -/
def rejected : Realization signature.{t, u, v} :=
  realize signature (fun _ p g => letI := rclike p; letI := group p;
    Set.indicator {(1 : carrier p)} 1 g) (fun e => nomatch e)

/-- The coefficient of the sign representation on the real line takes the value `1` at the
identity and `-1` at the other element. -/
theorem dependence : ObservationalDependence signature.{t, u, v} actual := by
  intro i
  cases i
  refine ⟨⟨LiftReal.{t}, Two.{u}, RLine.{v}, inferInstance, inferInstance, inferInstance,
    inferInstance, signRep LiftReal.{t} RLine.{v}, coordR, 1⟩, 1, flip, ?_⟩
  change coordR (signRep.{u} LiftReal.{t} RLine.{v} 1 1) ≠
    coordR (signRep.{u} LiftReal.{t} RLine.{v} flip 1)
  rw [signRep_flip, map_neg,
    show signRep.{u} LiftReal.{t} RLine.{v} 1 = 1 from map_one _, Module.End.one_apply]
  intro h
  have h1 := congrArg ULift.down h
  change (1 : ℝ) = -1 at h1
  norm_num at h1

set_option linter.checkUnivs false in
/-- Retain the complete telescope of `integral_dual_mul_dual_inv_eq_zero`. -/
abbrev arena : Arena where
  signature := signature.{t, u, v}
  Law r := ∀ {𝕜 : Type t} {G : Type u} {V : Type v} {W : Type w} [i𝕜 : RCLike 𝕜] [iG : Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasure μ]
    [iV : NormedAddCommGroup V] [iS : NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V] [AddCommGroup W]
    [Module 𝕜 W] (ρ : Representation 𝕜 G V) (σ : Representation 𝕜 G W) [ρ.IsIrreducible]
    [σ.IsIrreducible],
    IsEmpty (ρ.Equiv σ) → (∀ v, Continuous fun g => ρ g v) →
      ∀ (φ : Module.Dual 𝕜 V) (ψ : Module.Dual 𝕜 W), (∀ w, Continuous fun g => ψ (σ g w)) →
        ∀ (v : V) (w : W),
          ∫ g, r.readout () ⟨𝕜, G, V, i𝕜, iG, iV, iS, ρ, φ, v⟩ g * ψ (σ g⁻¹ w) ∂μ = 0

/-- With the indicator of the identity in place of the coefficient of the sign representation
on the real line, paired with the trivial representation, the integral is the positive mass of
the identity. -/
theorem rejected_law : ¬ arena.{t, u, v, w}.Law rejected := by
  intro h
  let _ := twoTop.{u}
  have := twoDiscrete.{u}
  have := twoTopGroup.{u}
  have := twoCompact.{u}
  let _ : MeasurableSpace Two.{u} := borel Two.{u}
  have : BorelSpace Two.{u} := ⟨rfl⟩
  have := rline_finiteDimensional.{t, v}
  have := signR_irreducible.{t, u, v}
  have := trivialR_irreducible.{t, u, w}
  have hz := h (𝕜 := LiftReal.{t}) (G := Two.{u}) (V := RLine.{v}) (W := RLine.{w})
    (Measure.haar) (signRep LiftReal.{t} RLine.{v})
    (Representation.trivial LiftReal.{t} Two.{u} RLine.{w})
    (signRep_not_equiv_trivial LiftReal.{t} two_ne_zero_liftReal RLine.{v} RLine.{w})
    (fun _ => continuous_of_discreteTopology) coordR coordR
    (fun _ => continuous_of_discreteTopology) 1 1
  apply integral_indicator_one_ne_zero (𝕜 := LiftReal.{t}) (Measure.haar : Measure Two.{u})
  rw [← hz]
  congr 1
  funext g
  change _ = _ * coordR.{t, w} (1 : RLine.{w})
  rw [coordR_one, mul_one]
  rfl

/-- The exact statement of `integral_dual_mul_dual_inv_eq_zero`. -/
abbrev sourceStatement : Prop := type_of% @integral_dual_mul_dual_inv_eq_zero.{t, u, v, w}

def source_registration : Registration arena.{t, u, v, w} sourceStatement.{t, u, v, w} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integral_dual_mul_dual_inv_eq_zero.{t, u, v, w}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end CoefficientField

/-! ## One representation: the coefficient `g ↦ φ (ρ g v)` over `ℂ` -/
namespace Coefficient

set_option linter.checkUnivs false in
/-- The data of the matrix coefficient `g ↦ φ (ρ g v)` of a representation on a complex normed
space. -/
abbrev Params : Type (max (u + 1) (v + 1)) :=
  Σ G : Type u, Σ V : Type v, Σ _ : Group G, Σ _ : NormedAddCommGroup V, Σ _ : NormedSpace ℂ V,
    Σ _ : Representation ℂ G V, Σ _ : Module.Dual ℂ V, V

/-- The group of a coefficient datum. -/
@[reducible] def carrier (p : Params.{u, v}) : Type u := p.1

/-- The space of a coefficient datum. -/
@[reducible] def space (p : Params.{u, v}) : Type v := p.2.1

/-- The data of a coefficient datum after its types. -/
def rest₁ (p : Params.{u, v}) : Σ iG : Group (carrier p), Σ iV : NormedAddCommGroup (space p),
    Σ iS : (letI := iV; NormedSpace ℂ (space p)),
    Σ _ : (letI := iG; letI := iV; letI := iS; Representation ℂ (carrier p) (space p)),
    Σ _ : (letI := iV; letI := iS; Module.Dual ℂ (space p)), space p :=
  p.2.2

/-- The group structure of a coefficient datum. -/
@[reducible] def group (p : Params.{u, v}) : Group (carrier p) := (rest₁ p).1

/-- The data of a coefficient datum after its group structure. -/
def rest₂ (p : Params.{u, v}) : Σ iV : NormedAddCommGroup (space p),
    Σ iS : (letI := iV; NormedSpace ℂ (space p)),
    Σ _ : (letI := group p; letI := iV; letI := iS; Representation ℂ (carrier p) (space p)),
    Σ _ : (letI := iV; letI := iS; Module.Dual ℂ (space p)), space p :=
  (rest₁ p).2

/-- The norm of the space of a coefficient datum. -/
@[reducible] def normed (p : Params.{u, v}) : NormedAddCommGroup (space p) := (rest₂ p).1

/-- The data of a coefficient datum after its norm. -/
def rest₃ (p : Params.{u, v}) : Σ iS : (letI := normed p; NormedSpace ℂ (space p)),
    Σ _ : (letI := group p; letI := normed p; letI := iS;
      Representation ℂ (carrier p) (space p)),
    Σ _ : (letI := normed p; letI := iS; Module.Dual ℂ (space p)), space p :=
  (rest₂ p).2

/-- The complex normed space structure of a coefficient datum. -/
@[reducible] def normedSpace (p : Params.{u, v}) :
    letI := normed p; NormedSpace ℂ (space p) := (rest₃ p).1

/-- The data of a coefficient datum after its normed space structure. -/
def rest₄ (p : Params.{u, v}) :
    Σ _ : (letI := group p; letI := normed p; letI := normedSpace p;
      Representation ℂ (carrier p) (space p)),
    Σ _ : (letI := normed p; letI := normedSpace p; Module.Dual ℂ (space p)), space p :=
  (rest₃ p).2

/-- The representation of a coefficient datum. -/
def rep (p : Params.{u, v}) :
    letI := group p; letI := normed p; letI := normedSpace p
    Representation ℂ (carrier p) (space p) := (rest₄ p).1

/-- The functional and the vector of a coefficient datum. -/
def rest₅ (p : Params.{u, v}) :
    Σ _ : (letI := normed p; letI := normedSpace p; Module.Dual ℂ (space p)), space p :=
  (rest₄ p).2

/-- The functional of a coefficient datum. -/
def dual (p : Params.{u, v}) :
    letI := normed p; letI := normedSpace p; Module.Dual ℂ (space p) := (rest₅ p).1

/-- The vector of a coefficient datum. -/
def vec (p : Params.{u, v}) : space p := (rest₅ p).2

/-- The matrix coefficient `g ↦ φ (ρ g v)` of a representation on a complex normed space. -/
abbrev signature : Signature where
  Params := Params.{u, v}
  State p := carrier p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u, v} :=
  realize signature (fun _ p g => letI := group p; letI := normed p; letI := normedSpace p;
    dual p (rep p g (vec p))) (fun e => nomatch e)

/-- The indicator of the identity element, read in place of every coefficient. -/
def rejected : Realization signature.{u, v} :=
  realize signature (fun _ p g => letI := group p; Set.indicator {(1 : carrier p)} 1 g)
    (fun e => nomatch e)

/-- The coefficient of the sign representation takes the value `1` at the identity and `-1` at
the other element. -/
theorem dependence : ObservationalDependence signature.{u, v} actual := by
  intro i
  cases i
  refine ⟨⟨Two.{u}, Line.{v}, inferInstance, inferInstance, inferInstance, sign.{u, v}, coord,
    1⟩, 1, flip, ?_⟩
  change coord (sign.{u, v} 1 1) ≠ coord (sign.{u, v} flip 1)
  rw [signRep_flip, map_one sign.{u, v}, Module.End.one_apply]
  change (1 : ℂ) ≠ -1
  norm_num

/-- Retain the complete telescope of `integral_dual_mul_dual_inv_self`. -/
abbrev arena : Arena where
  signature := signature.{u, v}
  Law r := ∀ {G : Type u} {V : Type v} [iG : Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasure μ] [iV : NormedAddCommGroup V]
    [iS : NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    [ρ.IsIrreducible], (∀ v, Continuous fun g => ρ g v) →
      ∀ (φ ψ : Module.Dual ℂ V) (v w : V),
        ∫ g, r.readout () ⟨G, V, iG, iV, iS, ρ, φ, v⟩ g * ψ (ρ g⁻¹ w) ∂μ =
          (μ.real Set.univ : ℂ) * (φ w * ψ v) / Module.finrank ℂ V

/-- With the indicator of the identity in place of the coefficient of the trivial representation
and the zero functional for `φ`, the left side is the positive mass of the identity while the
right side is `0`, for a Haar measure on the two-element group. -/
theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  let _ := twoTop.{u}
  have := twoDiscrete.{u}
  have := twoTopGroup.{u}
  have := twoCompact.{u}
  let _ : MeasurableSpace Two.{u} := borel Two.{u}
  have : BorelSpace Two.{u} := ⟨rfl⟩
  have := line_finiteDimensional.{v}
  have := trivial_irreducible.{u, v}
  have hz := h (G := Two.{u}) (V := Line.{v}) (Measure.haar : Measure Two.{u})
    (Representation.trivial ℂ Two.{u} Line.{v}) (fun _ => continuous_of_discreteTopology)
    0 coord 1 1
  apply integral_indicator_one_ne_zero (𝕜 := ℂ) (Measure.haar : Measure Two.{u})
  simp only [LinearMap.zero_apply, zero_mul, mul_zero, zero_div] at hz
  rw [← hz]
  congr 1
  funext g
  change _ = _ * coord (1 : Line.{v})
  change _ = _ * (1 : ℂ)
  rw [mul_one]
  rfl

/-- The exact statement of `integral_dual_mul_dual_inv_self`. -/
abbrev sourceStatement : Prop := type_of% @integral_dual_mul_dual_inv_self.{u, v}

def source_registration : Registration arena.{u, v} sourceStatement.{u, v} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@integral_dual_mul_dual_inv_self.{u, v}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

end Coefficient

def integral_dual_mul_dual_inv_eq_zero_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@integral_dual_mul_dual_inv_eq_zero.{t, u, v, w})
      (Realization CoefficientField.signature.{t, u, v}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality.integral_dual_mul_dual_inv_eq_zero_unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality.CoefficientField.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨CoefficientField.arena.{t, u, v, w}⟩
  objectArena := .source ⟨CoefficientField.arena.{t, u, v, w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source CoefficientField.arena.{t, u, v, w}
    ⟨CoefficientField.source_registration.{t, u, v, w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize CoefficientField.signature.{t, u, v}
    (fun _ p g => letI := CoefficientField.rclike p; letI := CoefficientField.group p;
      letI := CoefficientField.normed p; letI := CoefficientField.normedSpace p;
      CoefficientField.dual p (CoefficientField.rep p g (CoefficientField.vec p)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality
    definition := none
    coordinates := #[0, 1, 2, 19, 25, 28]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 30
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def integral_dual_mul_dual_inv_self_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@integral_dual_mul_dual_inv_self.{u, v}) (Realization Coefficient.signature.{u, v})
      Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality.integral_dual_mul_dual_inv_self_unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality.Coefficient.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Coefficient.arena.{u, v}⟩
  objectArena := .source ⟨Coefficient.arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Coefficient.arena.{u, v} ⟨Coefficient.source_registration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Coefficient.signature.{u, v}
    (fun _ p g => letI := Coefficient.group p; letI := Coefficient.normed p;
      letI := Coefficient.normedSpace p;
      Coefficient.dual p (Coefficient.rep p g (Coefficient.vec p))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality
    definition := none
    coordinates := #[0, 1, 14, 17, 19]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 21
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Analysis.CompactGroups.SchurOrthogonality

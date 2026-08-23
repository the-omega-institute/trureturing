/- GID: D5/S3/ConceptDynamics/Identity/MultilayerIdentityInsufficiency
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Identity/MultilayerIdentityInsufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Noninjective layers lose recovery and admit nonunique quotient choices. -/

import Mathlib.Data.Fintype.Order
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'noninjective_layer_cannot_recover' D5 Golden/Frozen/accepted`
     returned no matches.
   * The requested repository searches for pro-objects, inverse limits, cones,
     compatible families, `LeftInverse`, and `Injective` found no theorem covering
     noninjective recovery together with nonunique fibre-constant assignments.
   * `ConceptRelativeIdentity` treats kernels of readouts, while `FiniteStageReadout`
     and `ConceptAnchorHomAsymmetry` concern categorical stage representatives and
     Hom calculations; none supplies the present compatible-family construction.
   * Pinned Mathlib provides `Function.LeftInverse.injective` and
     `Function.not_injective_iff`. The first is reused to rule out recovery, and the
     second supplies a domain witness distinguishing two constant quotient choices.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Identity.MultilayerIdentityInsufficiency

universe u v w

/-- A multilayer subject is a family of layer states compatible with every downward
projection. -/
def CompatibleFamily {ι : Type u} [Preorder ι] (S : ι -> Type v)
    (p : forall i j, i <= j -> S j -> S i) :=
  {s : forall i, S i // forall i j (h : i <= j), p i j h (s j) = s i}

/-- A high-level assignment is a legal quotient of a projection when it is constant
on every fibre of that projection. -/
def FiberConstant {Sj : Type u} {Si : Type v} {Norm : Type w}
    (p : Sj -> Si) (q : Sj -> Norm) : Prop :=
  forall a b, p a = p b -> q a = q b

/-- A concrete two-layer state family: the lower layer is trivial and the upper
layer carries one bit. -/
def twoLayerState (i : Fin 2) : Type :=
  if i = 0 then Unit else Bool

/-- The downward maps of the concrete two-layer family forget the upper bit. -/
def twoLayerProjection (i j : Fin 2) (h : i <= j) :
    twoLayerState j -> twoLayerState i := by
  by_cases hi : i = 0
  · subst i
    exact fun _ => ()
  · have hi_one : i = 1 := by omega
    have hj_one : j = 1 := by omega
    subst i
    subst j
    exact id

/-- Each bit determines a compatible subject in the concrete two-layer family. -/
def twoLayerSubject (b : Bool) : CompatibleFamily twoLayerState twoLayerProjection := by
  refine ⟨fun i => ?_, ?_⟩
  · by_cases hi : i = 0
    · subst i
      exact ()
    · have hi_one : i = 1 := by omega
      subst i
      exact b
  · intro i j h
    by_cases hi : i = 0
    · subst i
      rfl
    · have hi_one : i = 1 := by omega
      have hj_one : j = 1 := by omega
      subst i
      subst j
      rfl

/-- The concrete cone is inhabited, but its lower component cannot distinguish its
two subjects with different upper bits. -/
theorem two_layer_cone_nonempty_and_loses_high_information :
    Nonempty (CompatibleFamily twoLayerState twoLayerProjection) /\
      exists x y : CompatibleFamily twoLayerState twoLayerProjection,
        x.1 0 = y.1 0 /\ Not (x.1 1 = y.1 1) := by
  refine ⟨⟨twoLayerSubject false⟩,
    twoLayerSubject false, twoLayerSubject true, ?_, ?_⟩
  · rfl
  · exact Bool.false_ne_true

/-- A noninjective layer projection has no left inverse. Moreover, whenever the
normative identity type has two distinct values, two distinct legal quotient
assignments exist, so the reverse high-level choice is not automatic. -/
theorem noninjective_layer_cannot_recover {Sj : Type u} {Si : Type v}
    {Norm : Type w} (p : Sj -> Si) (hp : Not (Function.Injective p))
    (n1 n2 : Norm) (hne : Not (n1 = n2)) :
    (Not (exists r : Si -> Sj, Function.LeftInverse r p)) /\
      exists q1 q2 : Sj -> Norm,
        FiberConstant p q1 /\ FiberConstant p q2 /\ Not (q1 = q2) := by
  rcases Function.not_injective_iff.mp hp with ⟨a, b, hab, hab_ne⟩
  constructor
  · rintro ⟨r, hr⟩
    exact hp hr.injective
  · refine ⟨fun _ => n1, fun _ => n2, ?_, ?_, ?_⟩
    · intro x y hxy
      rfl
    · intro x y hxy
      rfl
    · intro hq
      exact hne (congrFun hq a)

example :
    (Not (exists r : Unit -> Bool,
      Function.LeftInverse r (fun _ : Bool => ()))) /\
      exists q1 q2 : Bool -> Bool,
        FiberConstant (fun _ : Bool => ()) q1 /\
          FiberConstant (fun _ : Bool => ()) q2 /\ Not (q1 = q2) := by
  exact noninjective_layer_cannot_recover (fun _ : Bool => ())
    Function.not_injective_const false true Bool.false_ne_true

#print axioms noninjective_layer_cannot_recover

end D5.S3.ConceptDynamics.Identity.MultilayerIdentityInsufficiency

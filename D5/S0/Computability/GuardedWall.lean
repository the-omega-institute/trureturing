/- GID: D5/S0/Computability/GuardedWall
   generality: G
   mirror-B: D5/B/S0/Computability/GuardedWall
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Guarded statements never enter a forbidden positive configuration. -/

module
prelude
public import OmegaInit.Core

namespace D5.S0.Computability.GuardedWall

open Omega

universe u v

/-- A wall statement cannot become positive when its positive gatekeepers make
that configuration forbidden and consistency rules out forbidden configurations. -/
public theorem wall_never_positive
    {Time : Sort u} {Statement : Type v}
    (positive : Time → Statement → Prop)
    (wall gatekeepers : Statement → Prop)
    (forbidden : Time → Statement → Prop)
    (gatekeepers_positive : ∀ t g, gatekeepers g → positive t g)
    (joint_positive_forbidden : ∀ t w, wall w → positive t w →
      (∀ g, gatekeepers g → positive t g) → forbidden t w)
    (consistent : ∀ t w, wall w → Not (forbidden t w)) :
    ∀ t w, wall w → Not (positive t w) :=
  fun t w inWall positiveNow => consistent t w inWall
    (joint_positive_forbidden t w inWall positiveNow (gatekeepers_positive t))

/-- A one-step Boolean ledger witnesses the hypotheses and wall membership. -/
public theorem boolean_guarded_wall_witness :
    let positive : Omega.True → Bool → Prop := fun _ statement => Eq statement .true
    let wall : Bool → Prop := fun statement => Eq statement .false
    let gatekeepers : Bool → Prop := fun statement => Eq statement .true
    let forbidden : Omega.True → Bool → Prop := fun _ statement =>
      Omega.And (Eq statement Bool.false) (Eq statement Bool.true)
    Omega.And (∀ t g, gatekeepers g → positive t g)
      (Omega.And (∀ t w, wall w → positive t w →
          (∀ g, gatekeepers g → positive t g) → forbidden t w)
        (Omega.And (∀ t w, wall w → Not (forbidden t w))
          (Omega.And (wall .false) (Not (positive Omega.True.intro .false))))) :=
  have falseNeTrue : Not (Eq Bool.false Bool.true) :=
    fun h => Eq.subst (motive := Bool.rec (motive := fun _ => Prop) Omega.True False) h Omega.True.intro
  Omega.And.intro (fun _ _ gatekeeper => gatekeeper)
    (Omega.And.intro (fun _ _ inWall positiveNow _ => Omega.And.intro inWall positiveNow)
      (Omega.And.intro (fun _ _ _ evidence => falseNeTrue (evidence.left.symm.trans evidence.right))
        (Omega.And.intro rfl falseNeTrue)))

end D5.S0.Computability.GuardedWall

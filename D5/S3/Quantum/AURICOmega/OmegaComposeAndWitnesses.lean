/- GID: D5/S3/Quantum/AURICOmega/OmegaComposeAndWitnesses
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/OmegaComposeAndWitnesses
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formal composition, Cayley trigonometry and exact algebraic and FRACTRAN witnesses. -/

module
prelude
public import OmegaMath.Calculus.DFiniteCompose
public import OmegaMath.Witnesses.FlagshipWitnesses

namespace D5.S3.Quantum.AURICOmega.OmegaComposeAndWitnesses

open Omega
open Omega.JetSeq

public theorem deriv_compose_equivAt (N : Nat) (f g : JetSeq) (hf : Finite f) (hg : Finite g)
    (g0 : IntRatio.Equivalent (g Nat.zero) IntRatio.zero) :
    EquivalentAt N (deriv (compose f g)) (mul (compose (deriv f) g) (deriv g)) :=
  JetSeq.deriv_compose_equivAt N f g hf hg g0

public theorem cos_two_atan_eq_cayley (N : Nat) :
    EquivalentAt N (compose Cos (smul IntRatio.two Atan)) CayleyCos :=
  JetSeq.cos_two_atan_eq_cayley N

public theorem sin_two_atan_eq_cayley (N : Nat) :
    EquivalentAt N (compose Sin (smul IntRatio.two Atan)) CayleySin :=
  JetSeq.sin_two_atan_eq_cayley N

public theorem mat2_det_mul (A B : Mat2) : Eq (A.mul B).det (A.det.mul B.det) :=
  Omega.mat2_det_mul A B

public theorem phalf_qhalf_noncommutative :
    Not (Ternion.RayEquiv (Ternion.triad Ternion.pHalf Ternion.p0 Ternion.qHalf)
      (Ternion.triad Ternion.qHalf Ternion.p0 Ternion.pHalf)) :=
  Omega.phalf_qhalf_noncommutative

public theorem g120_spin_six_beat_orbit : PythSpinor.SixBeatOrbit :=
  PythSpinor.g120_spin_six_beat_orbit

public theorem orthogonal_triad_excess_quarter :
    IntRatio.Equivalent
      (Geometry.BargmannGram.detGram3 Geometry.BargmannGram.Quad4.one
        Geometry.BargmannGram.pHalf Geometry.BargmannGram.qHalf)
      (IntRatio.value Int.one Nat.one.succ.succ.succ) :=
  Omega.orthogonal_triad_excess_quarter

open Omega.Fractran

private theorem running_before_trace_end (prog : Program) (states : Arithmetic.NatList) :
    ∀ n k, Follows prog states n → Nat.lt k (traceLength states) →
      Not (Halts prog (run prog k n)) :=
  Arithmetic.NatList.rec
    (motive := fun states => ∀ n k, Follows prog states n → Nat.lt k (traceLength states) →
      Not (Halts prog (run prog k n)))
    (fun _ k _ hk => False.elim (Nat.not_succ_le_zero k hk))
    (fun next rest ih n k trace =>
      Nat.rec (motive := fun k => Nat.lt k (traceLength (.cons next rest)) →
        Not (Halts prog (run prog k n)))
        (fun _ halted => Result.none_ne_some next
          (((halts_iff prog n).mp halted).symm.trans (Step.sound trace.left)))
        (fun j _ hj halted =>
          have stepped := (run_succ_first prog j n).trans
            (congrArg (run prog j) (advance_of_step trace.left))
          ih next j trace.right hj (Eq.subst (Halts prog) stepped halted)) k) states

/-- The listed fifteen transitions reach 22, the first state at which every guard fails. -/
public theorem p_omega_halts_at_22 :
    And (Follows pOmega pOmegaTrace pOmegaStart)
      (And (Eq (run pOmega (appendDigit Nat.one five) pOmegaStart) pOmegaFinal)
        (And (Halts pOmega pOmegaFinal)
          (∀ k, Nat.lt k (appendDigit Nat.one five) → Not (Halts pOmega (run pOmega k pOmegaStart))))) :=
  have runWitness := Fractran.p_omega_halts_at_22
  And.intro runWitness.left (And.intro runWitness.right.left
    (And.intro runWitness.right.right
      (fun k hk => running_before_trace_end pOmega pOmegaTrace pOmegaStart k runWitness.left hk)))

end D5.S3.Quantum.AURICOmega.OmegaComposeAndWitnesses

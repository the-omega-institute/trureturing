/- GID: D5/S3/Geometry/ProjectionRange/UniformTransport
   generality: G
   mirror-B: D5/B/S3/Geometry/ProjectionRange/UniformTransport
   mirror-E: none(waiver:pure-structural-proof)
   anchors: []
   utility: none
   digest: Invertible intertwiners for continuous idempotents. -/
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Connected.Clopen

noncomputable section
open Filter Topology

namespace ProjectionRange.UniformTransport

private def shuffle {R : Type*} [Ring R] (p q : R) : R :=
  q * p + (1 - q) * (1 - p)

private theorem shuffle_self {R : Type*} [Ring R] (p : R) (hp : p * p = p) :
    shuffle p p = 1 := by
  dsimp [shuffle]
  rw [hp, mul_sub, mul_one, sub_mul, one_mul, hp, sub_self, sub_zero]
  simp only [← add_sub_assoc, add_sub_cancel_left]

private theorem shuffle_intertwines {R : Type*} [Ring R] (p q : R)
    (hp : p * p = p) (hq : q * q = q) :
    q * shuffle p q = shuffle p q * p := by
  have hq0 : q * (1 - q) = 0 := by rw [mul_sub, mul_one, hq, sub_self]
  have hp0 : (1 - p) * p = 0 := by rw [sub_mul, one_mul, hp, sub_self]
  dsimp [shuffle]
  rw [mul_add, add_mul, ← mul_assoc q q p, hq,
    ← mul_assoc q (1 - q) (1 - p), hq0, zero_mul, add_zero,
    mul_assoc q p p, hp, mul_assoc (1 - q) (1 - p) p, hp0, mul_zero, add_zero]

/-- Continuous idempotents over a preconnected parameter space have an invertible
ambient intertwiner between any two parameters. In a continuous-map Banach algebra,
unit openness supplies a single uniform neighborhood over the entire compact base.
No subdivision, invertibility, or frame is an input. -/
theorem connected_idempotents_intertwiner
    {T R : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    [NormedRing R] [CompleteSpace R]
    (P : T → R) (hP : Continuous P) (hidem : ∀ t, P t * P t = P t)
    (s t : T) : ∃ u : Rˣ, P t * (u : R) = (u : R) * P s := by
  let Rel : T → T → Prop := fun a b =>
    ∃ u : Rˣ, P b * (u : R) = (u : R) * P a
  have hlocal (a : T) : ∀ᶠ b in 𝓝 a, Rel a b ∧ Rel b a := by
    have hc : Continuous (fun b => shuffle (P a) (P b)) :=
      (hP.mul continuous_const).add
        ((continuous_const.sub hP).mul continuous_const)
    have hunit : IsUnit (shuffle (P a) (P a)) := by
      rw [shuffle_self _ (hidem a)]
      exact isUnit_one
    have hu : ∀ᶠ b in 𝓝 a, IsUnit (shuffle (P a) (P b)) :=
      hc.continuousAt.eventually (Units.isOpen.mem_nhds hunit)
    filter_upwards [hu] with b hb
    obtain ⟨u, hu⟩ := hb
    have h : P b * (u : R) = (u : R) * P a := by
      rw [hu]
      exact shuffle_intertwines _ _ (hidem a) (hidem b)
    refine ⟨⟨u, h⟩, u⁻¹, ?_⟩
    have h' := congrArg (fun z : R => (↑u⁻¹ : R) * z * (↑u⁻¹ : R)) h
    simpa [mul_assoc] using h'.symm
  have htrans : IsTrans T Rel := ⟨by
    intro a b c hab hbc
    obtain ⟨u, hu⟩ := hab
    obtain ⟨v, hv⟩ := hbc
    refine ⟨v * u, ?_⟩
    change P c * ((v : R) * (u : R)) = ((v : R) * (u : R)) * P a
    rw [← mul_assoc, hv, mul_assoc, hu, ← mul_assoc]⟩
  exact PreconnectedSpace.induction₂' Rel hlocal htrans s t

end ProjectionRange.UniformTransport

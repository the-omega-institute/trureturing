/- GID: D5/S3/Arith/HiddenFiberRigidity
   generality: I
   mirror-B: D5/B/S3/Arith/HiddenFiberRigidity
   mirror-E: none(waiver:analytic-proof-only)
   anchors: []
   digest: A continuous map from a connected real interval into the profinite fiber product is constant. -/
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Connected.TotallyDisconnected

namespace D5.S3.Arith.HiddenFiberRigidity

open Set

/-- A prime bundled in `Nat.Primes` carries the primality fact needed to form
its ring of `p`-adic integers `ℤ_[p]`; this promotes the packaged proof `p.2`
to the `Fact` witness required by the `PadicInt` construction. -/
private instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- **Hidden fiber rigidity.** Any map that is continuous on a
preconnected subset `s` of the real line, valued in the profinite fiber
product `K_∞ = ∏_p ℤ_p`, is constant on `s`.

The proof is the profinite reading of the informal argument. The product
topology makes each coordinate projection continuous, so continuity is exactly
coordinatewise continuity. Each factor `ℤ_[p]` is an ultrametric space, hence
totally separated and a fortiori totally disconnected; the product of totally
disconnected spaces is totally disconnected (`Pi.totallyDisconnectedSpace`).
The continuous image `f '' s` of the preconnected set `s` is preconnected
(`IsPreconnected.image`), and a preconnected subset of a totally disconnected
space is a subsingleton (`IsPreconnected.subsingleton`). Hence any two values
`f x` and `f y` with `x, y ∈ s` coincide.

The domain hypothesis `IsPreconnected s` is the exact characterization of the
"connected real interval" of the statement: the preconnected subsets of `ℝ`
are precisely its intervals, so no generality is lost or gained by phrasing the
domain as an arbitrary preconnected set. -/
theorem hidden_fiber_rigidity
    {s : Set ℝ} (hs : IsPreconnected s)
    (f : ℝ → ∀ p : Nat.Primes, ℤ_[p.1]) (hf : ContinuousOn f s) :
    ∀ x ∈ s, ∀ y ∈ s, f x = f y := fun _ hx _ hy =>
  (hs.image f hf).subsingleton (mem_image_of_mem f hx) (mem_image_of_mem f hy)

end D5.S3.Arith.HiddenFiberRigidity

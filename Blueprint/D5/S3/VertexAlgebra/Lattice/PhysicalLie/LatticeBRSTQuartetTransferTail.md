# Constant-term compression of every finite original quartet transfer polynomial

## Abstract

Constant-term compression of every finite original quartet transfer polynomial

Let D : LatticeData, F : NullFrame D, t : Nat and B : Module.Basis (Fin t) Complex F.K. Let H : Matrix (Fin D.rank) (Fin D.rank) Complex satisfy both hHG : H * gramComplex D = 1 and hGH : gramComplex D * H = 1. The carrier is the original matter tensor occupation-ghost space State D. The null frame and its chosen transverse basis are retained throughout.

P0 = P0 F B is the actual zero-count projector in actualBasis F B. Its surviving basis indices have no longitudinal exponents and ghost occupation {1} or {1,3}; their signed degrees are respectively 0 and 1. Both occupations remain, with arbitrary transverse monomials and original integral lattice charges.

Fix any integral charge p : Charge D and any N : Nat with 1 ≤ N. Write delta = Q - d0 F p, A = h F B p * delta, and Pi_p = chargeProject p. The actual homotopy is h F B p = R F p * invM F B. The finite polynomial is inversePolynomial A N = sum over 0 ≤ j < N of (-A)^j. The result is P0 * delta * inversePolynomial A N * P0 * Pi_p = P0 * delta * P0 * Pi_p, an endomorphism identity on all original State D.

The charge p is arbitrary, including pPlus p = 0, and every finite positive length N is covered. No relative b0 condition, mass shell, fixed energy, critical rank, nilpotence, convergence or infinite-series assumption enters the statement.

Canonical declaration: D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTQuartetTransferTail.full_original_finite_transfer_compression. Source declaration: D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTQuartetTransferTail.full_original_finite_transfer_compression.

**Theorem 1.1 (Every positive finite length has the same compressed constant term).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTQuartetTransferTail.full_original_finite_transfer_compression`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTQuartetTransferTail.full_original_finite_transfer_compression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source notation and complete enclosing context:

```lean

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTFullOriginalRaising

import D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction

import D5.S3.HomologicalAlgebra.FinitePerturbation

/-!

The original full Q, actual h = R * invM, and zero-count P0 are used on

ALL original states. Both ghost occupations {1} and {1,3} remain present:

their signed degrees are respectively 0 and 1. No b0 condition is imposed.

The power induction follows the support-raising induction in the pinned

LatticeRelativeBRSTCohomology.h_full_remainder_nilpotent_on_relativeMassShell.

Here it uses only fixed charge and a lower degree bound, without the shell,

its upper bound, or nilpotence. This absolute compression theorem leaves the

leading original-Q compression unevaluated.

-/

set_option autoImplicit false

set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTQuartetTransferTail

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeLightConeCoordinates

open LatticeLightConeCoordinates.NullFrame LatticeQuartetContraction

open LatticeBRSTModeFiltration LatticeBRSTFullOriginalRaising

open D5.S3.Quantum.Fermionic.BcGhostCharge

open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus

open D5.S3.HomologicalAlgebra

variable {D : LatticeData} (F : NullFrame D) {t : ℕ}

variable (B : Module.Basis (Fin t) ℂ F.K)

```

### Exact written theorem header through its outer assignment:

```lean

theorem full_original_finite_transfer_compression

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

    (p : Charge D) (N : ℕ) (hN : 1 ≤ N) :

    P0 F B * (LatticeBRST.totalCharge D H - d0 F p) *

        FinitePerturbation.inversePolynomial

          (h F B p * (LatticeBRST.totalCharge D H - d0 F p)) N *

        P0 F B * chargeProject p =

      P0 F B * (LatticeBRST.totalCharge D H - d0 F p) *

        P0 F B * chargeProject p := by

```

### Local definitions retained at the start of the proof:

```lean

  classical

  let delta : Module.End ℂ (State D) := LatticeBRST.totalCharge D H - d0 F p

  let A : Module.End ℂ (State D) := h F B p * delta

  change P0 F B * delta * FinitePerturbation.inversePolynomial A N *

      P0 F B * chargeProject p = P0 F B * delta * P0 F B * chargeProject p

```

The diagonal actions of the genuine P0 and chargeProject show that y = P0(Pi_p v) has fixed charge p and all nonzero coefficients have degree at least 0. The full_remainder_fixed_charge_vectors supplier says that both delta and h*delta preserve p and raise a lower degree bound by one. Induction therefore gives degree at least r on A^r y. For r ≥ 1, the extra delta gives degree at least r+1 ≥ 2, which P0 kills because its actual zero-count support has only degrees 0 and 1. Thus P0*delta*A^r*P0*Pi_p = 0 for every positive r.

The identity (-A)^j = ((-1 : Complex)^j) • A^j transfers this vanishing to the signed powers in inversePolynomial. Expanding the finite sum leaves only j = 0; the condition 1 ≤ N puts that index in Finset.range N. The constant power is the identity, giving exactly P0*delta*P0*Pi_p. This argument uses the lower degree bound for each finite iteration and never asks a power of A to vanish on the whole carrier.

The source credits the support-raising induction in LatticeRelativeBRSTCohomology.h_full_remainder_nilpotent_on_relativeMassShell. Here the induction tracks fixed charge and a lower degree bound. The finite inversePolynomial definition is supplied by FinitePerturbation, whose algebraic perturbation construction is attributed to Gugenheim–Lambe–Stasheff; the polynomial compression itself requires no nilpotence assumption.

In LatticeBRSTFullNonzeroAbsoluteCohomology.actual_transferred_compression this theorem is applied with N = vectorCutoff F B v.val and its proved positivity. It removes the positive terms in the actual transferred operator. The ground-compression theorem then evaluates the constant contribution; this tail theorem itself leaves P0*delta*P0*chargeProject unevaluated.

The operator provenance is the original Becchi–Rouet–Stora–Tyutin BRST construction, with Kato–Ogawa and Lian–Zuckerman attribution recorded by the supplied absolute-cohomology source. The lattice, current and occupation suppliers retain their Bakalov–Kac, Scott Carnahan and Kalle Kytölä attribution. Mathlib supplies the linear-map, basis, finite-support and finite-sum machinery. These credits describe the supplied constructions; they do not attribute this exact compression theorem to a separate literature source.

Mathematical suppliers: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration`; `D5/S3/VertexAlgebra/Lattice/LatticeBRSTFullOriginalRaising`; `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction`; `D5/S3/HomologicalAlgebra/FinitePerturbation`

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTQuartetTransferTail.full_original_finite_transfer_compression`
- Dependency: [D5/S3/HomologicalAlgebra/FinitePerturbation](../../../HomologicalAlgebra/FinitePerturbation.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTFullOriginalRaising](../LatticeBRSTFullOriginalRaising.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration](../LatticeBRSTModeFiltration.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction](../LatticeQuartetContraction.md)
- Narrative reference: [D5/S3/HomologicalAlgebra/FinitePerturbation](../../../HomologicalAlgebra/FinitePerturbation.md)
- Narrative reference: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTFullOriginalRaising](../LatticeBRSTFullOriginalRaising.md)
- Narrative reference: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTModeFiltration](../LatticeBRSTModeFiltration.md)
- Narrative reference: [D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction](../LatticeQuartetContraction.md)

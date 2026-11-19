# Original BRST charge on the full zero-count quartet ground

## Abstract

Original BRST charge on the full zero-count quartet ground

Let D : LatticeData, F : NullFrame D, t : Nat and B : Module.Basis (Fin t) Complex F.K. Let H : Matrix (Fin D.rank) (Fin D.rank) Complex satisfy both hHG : H * gramComplex D = 1 and hGH : gramComplex D * H = 1. The carrier is the original matter tensor occupation-ghost space State D. The null frame and its chosen transverse basis are retained throughout.

P0 = P0 F B is the actual zero-count projector in actualBasis F B. Its surviving basis indices have no longitudinal exponents and ghost occupation {1} or {1,3}; their signed degrees are respectively 0 and 1. Both occupations remain, with arbitrary transverse monomials and original integral lattice charges.

Write P = P0 F B, Q = LatticeBRST.totalCharge D H, b = ghostB D 0, c = ghostC D 0 and L = matterMode D H 0 + ghostVirasoro D 0. The result is the literal equality P * Q * P = P * c * L * P in Module.End Complex (State D), so it holds on every original state. The hypotheses are precisely the frame, basis and the two complex inverse-Gram equations; there is no fixed-charge, energy-shell, b0-kernel, critical-rank or positivity premise.

Canonical declaration: D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTQuartetGroundCompression.original_Q_ground_compression. Source declaration: D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTQuartetGroundCompression.original_Q_ground_compression.

**Theorem 1.1 (Literal full-state ground compression).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTQuartetGroundCompression.original_Q_ground_compression`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTQuartetGroundCompression.original_Q_ground_compression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source notation and complete enclosing context:

```lean

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTFullOriginalRaising

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTRelativeZeroMode

import Mathlib.Tactic

set_option autoImplicit false

set_option relaxedAutoImplicit false

set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTQuartetGroundCompression

open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality

open D5.S3.VertexAlgebra.LatticeMatterGhostCoupling

open D5.S3.VertexAlgebra.LatticeBRST

open D5.S3.VertexAlgebra.LatticeQuartetContraction

open D5.S3.VertexAlgebra.LatticeQuartetContraction.GC

open D5.S3.VertexAlgebra.LatticeBRSTModeFiltration

open D5.S3.VertexAlgebra.LatticeBRSTFullOriginalRaising

open D5.S3.VertexAlgebra.LatticeSugawaraCurrents

open D5.S3.VertexAlgebra.LatticeLightConeCoordinates

open D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame

open D5.S3.Quantum.Fermionic.CountableOccupationFock

open D5.S3.Quantum.Fermionic.BcGhostFock

open D5.S3.Quantum.Fermionic.BcGhostQuartetCount

open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus

variable {D : LatticeData} (F : NullFrame D) {t : ℕ}

variable (B : Module.Basis (Fin t) ℂ F.K)

```

### Exact written theorem header through its outer assignment:

```lean

theorem original_Q_ground_compression

    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :

    P0 F B * LatticeBRST.totalCharge D H * P0 F B =

      P0 F B * ghostC D 0 *

        (matterMode D H 0 + ghostVirasoro D 0) * P0 F B := by

```

### Local definitions retained at the start of the proof:

```lean

  let P : Module.End ℂ (LatticeQuartetContraction.State D) := P0 F B

  let Q : Module.End ℂ (LatticeQuartetContraction.State D) := LatticeBRST.totalCharge D H

  let C : Module.End ℂ (LatticeQuartetContraction.State D) := P * Q * P

  let b : Module.End ℂ (LatticeQuartetContraction.State D) := ghostB D 0

  let c : Module.End ℂ (LatticeQuartetContraction.State D) := ghostC D 0

  let L : Module.End ℂ (LatticeQuartetContraction.State D) :=

    matterMode D H 0 + ghostVirasoro D 0

```

For each actual basis vector, choose its own lattice charge in Q - d0. The supplier P0*d0 = 0 gives P0*Q*P0 = P0*(Q-d0)*P0. The fixed-charge basis-raising theorem raises every nonzero output coefficient by at least one in signed degree. After the left projection, both input and output degrees belong to {0,1}; hence the surviving output has degree 1 and occupation {1,3}. The actual c0 is signed creation at site 3, so it kills this output. Finite basis expansion proves c*(P*Q*P) = 0 on the entire original carrier.

The actual site-3 creation law preserves quartet count, so P*c = c*P. The supplied b0 commutation gives P*b = b*P. Put C = P*Q*P. The original Ward identity Q*b + b*Q = L compresses to C*b + b*C = P*L*P. The actual mixed zero-mode CAR b*c + c*b = 1, together with c*C = 0, gives C = c*b*C and c*(C*b + b*C) = C. Consequently C = c*P*L*P = P*c*L*P. These basis and noncommutative algebra steps evaluate the original Q compression; the public theorem is not an endpoint alias.

In LatticeBRSTFullNonzeroAbsoluteCohomology.actual_transferred_compression the literal theorem is evaluated at the original state underlying u. After the tail theorem removes the positive terms and d0 kills P0-fixed input, this equality supplies the final c0 times totalL0 expression. The downstream cohomology construction carries its own pPlus and rank-26 hypotheses; they are not assumptions of this compression identity.

The operator provenance is the original Becchi–Rouet–Stora–Tyutin BRST construction, with Kato–Ogawa and Lian–Zuckerman attribution recorded by the supplied absolute-cohomology source. The lattice, current and occupation suppliers retain their Bakalov–Kac, Scott Carnahan and Kalle Kytölä attribution. Mathlib supplies the linear-map, basis, finite-support and finite-sum machinery. These credits describe the supplied constructions; they do not attribute this exact compression theorem to a separate literature source.

Mathematical suppliers: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTFullOriginalRaising`; `D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode`; `D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction`; `D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard`

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTQuartetGroundCompression.original_Q_ground_compression`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTFullOriginalRaising](../LatticeBRSTFullOriginalRaising.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode](../LatticeBRSTRelativeZeroMode.md)
- Narrative reference: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTFullOriginalRaising](../LatticeBRSTFullOriginalRaising.md)
- Narrative reference: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeZeroMode](../LatticeBRSTRelativeZeroMode.md)
- Narrative reference: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard](../LatticeBRSTWard.md)
- Narrative reference: [D5/S3/VertexAlgebra/Lattice/LatticeQuartetContraction](../LatticeQuartetContraction.md)

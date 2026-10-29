# Ordinary two-current thermal resummation

## Abstract

The evaluated ordinary two-current thermal series of the original positive integral lattice fields on the entire split open bidisk.

Let D be the original integral even symmetric lattice datum with positive definite real Gram matrix, and let i,j be arbitrary current directions. Write Q(beta)=chargeEnergy(D,beta).toNat and N(d)=oscillatorEnergy(d). The charge ranges over every integral charge and d over every ordinary monomial occupation. Put q=q1*q2, where each complex qi has norm less than one. Either or both qi may vanish, and the cross Gram entry G(i,j) may have either sign.

**Definition 1.1 (Ordinary occupation character).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentThermal.oscillatorCharacter`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentThermal.oscillatorCharacter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Zosc(D,q) is the unrestricted sum of q^N(d). No reflection sign, factorial weight or finite occupation cutoff is inserted.

**Definition 1.2 (Natural-energy charge theta series).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentThermal.chargeTheta`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentThermal.chargeTheta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Theta(D,q) is the unrestricted sum over beta of q^Q(beta). Positive real Gram ensures that Q is the original nonnegative charge energy.

**Definition 1.3 (Charge second moment).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentThermal.chargeMoment`

*Formalization.* `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentThermal.chargeMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Theta_ij(D,q) is the unrestricted sum of bilinear(D,unitCharge(i),beta) times bilinear(D,unitCharge(j),beta) times q^Q(beta), with the two bilinear values cast to the complex numbers.

**Theorem 1.4 (Evaluated actual finite-grade trace series).**

Lean statement: `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentThermal.ordinary_two_current_thermal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentThermal.ordinary_two_current_thermal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all D, its real-Gram positivity proof, i,j,q1,q2 and proofs that both norms are below one, the family q1^n*q2^m*actualCurrentCycleTrace(D,hD,i,j,n,m) is norm-summable over every pair of natural grades. Its HasSum value is Zosc(D,q) times [Theta_ij(D,q) + G(i,j)*Theta(D,q)*sum_k (k+1)*(q1^(k+1)+q2^(k+1))/(1-q^(k+1))], where k ranges over all natural numbers and q=q1*q2. The trace is LinearMap.trace on the original finite full-energy grade of the composition of the original Y(currentState) grade compressions.

The full-charge loop theorem gives absolute convergence after identifying the original current compressions. Restricting its literal coefficient family to zero occupations gives separate absolute theta and charge-moment sums, using vacuum and zero-mode current fields respectively. Ordinary oscillator convergence follows by exact norm comparison with the signed occupation convergence theorem; its signed value is not used.

The diagonal is grouped by Q(beta)+N(d). For a positive frequency ell, the off-diagonal energy fiber Q(beta)+N(d)+k*ell=a is equivalent to the finite sum of beta in the original charge cutoff at a, k from zero through floor((a-Q(beta))/ell), and occupations of energy a-Q(beta)-k*ell. The bound therefore stays charge-dependent. This fiber identity consumes the complete finite two-current trace formula.

Joint absolute summability precedes regrouping. The marked family ell*x^ell*q^(k*ell) is bounded in norm by the product of the summable frequency family ell*norm(x)^ell and the geometric family norm(q)^k. Its geometric k sum is ell*x^ell/(1-q^ell). Diagonal, upper and lower energy regions are then embedded into all pairs of natural grades. Only natural powers occur, so the two zero faces are retained without taking an inverse of q1 or q2.

The lattice current normalization and original field constructions retain the Bakalov--Kac attribution of the finite trace theorem. This is an ordinary chiral lattice thermal identity. Annular continuation, ellipticity, modular covariance, sewing, nonchiral CFT, Monster completion, string consistency and an AdS/CFT correspondence require additional mathematics.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentThermal.chargeMoment`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentThermal.chargeTheta`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentThermal.ordinary_two_current_thermal`
- Truth anchor: `D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentThermal.oscillatorCharacter`
- Dependency: [D5/S3/VertexAlgebra/Characters/LatticeTwoCurrentTrace](LatticeTwoCurrentTrace.md)
- Dependency: [D5/S3/VertexAlgebra/Sewing/CanonicalFullChargeLoop](../Sewing/CanonicalFullChargeLoop.md)

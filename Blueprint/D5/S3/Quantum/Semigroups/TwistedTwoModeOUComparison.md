# Two-mode pure-state attenuation

## Abstract

The two literal Jordan-Wigner Kraus maps attenuate every complex unit pure state by a quartic budget.

Use the ordered basis 00,01,10,11. J is [[0,1],[0,0]] and Z is diag(-1,1). The modes are J tensor I and Z tensor J. Each H is the unital completely positive jumpMap from TwoKrausRankOneAttenuation, without a trace-preservation claim. All matrix, PSD and L2 operator norm carriers are the existing ones.

**Definition 1.1 (Literal fermionic modes).**

$$\forall i \in \operatorname{Fin}\left(2\right),\; \operatorname{modeJump}\left(i\right) = \operatorname{at}\left(\operatorname{pair}\left(\operatorname{kronecker}\left(\operatorname{matrix}\left(0, 1, 0, 0\right), 1\right), \operatorname{kronecker}\left(\operatorname{diagonal}\left(\operatorname{pair}\left(\operatorname{neg}\left(1\right), 1\right)\right), \operatorname{matrix}\left(0, 1, 0, 0\right)\right)\right), i\right)$$

*Formalization.* `D5/S3/Quantum/Semigroups/TwistedTwoModeOUComparison.modeJump` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both modes satisfy J_i squared=0 and J_i J_i*+J_i* J_i=I. The literal twist W=diag(1,1,-1,1) sends I tensor J to minus Z tensor J; the overall minus cancels in the Kraus sandwich. The proved bound uses the displayed modes directly and does not assert a separate twist-conjugation theorem.

**Definition 1.2 (Actual directional budget).**

$$\forall psi \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right)\right),\; \operatorname{directionalBudget}\left(psi\right) = \operatorname{add}\left(\operatorname{add}\left(\operatorname{pow}\left(\operatorname{add}\left(\operatorname{normSq}\left(\operatorname{at}\left(psi, \operatorname{pair}\left(0, 0\right)\right)\right), \operatorname{normSq}\left(\operatorname{at}\left(psi, \operatorname{pair}\left(0, 1\right)\right)\right)\right), 2\right), \operatorname{pow}\left(\operatorname{add}\left(\operatorname{normSq}\left(\operatorname{at}\left(psi, \operatorname{pair}\left(0, 0\right)\right)\right), \operatorname{normSq}\left(\operatorname{at}\left(psi, \operatorname{pair}\left(1, 0\right)\right)\right)\right), 2\right)\right), \operatorname{add}\left(\operatorname{mul}\left(2, \operatorname{normSq}\left(\operatorname{mul}\left(\operatorname{at}\left(psi, \operatorname{pair}\left(0, 0\right)\right), \operatorname{at}\left(psi, \operatorname{pair}\left(1, 1\right)\right)\right)\right)\right), \operatorname{mul}\left(2, \operatorname{normSq}\left(\operatorname{mul}\left(\operatorname{at}\left(psi, \operatorname{pair}\left(0, 1\right)\right), \operatorname{at}\left(psi, \operatorname{pair}\left(1, 0\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Semigroups/TwistedTwoModeOUComparison.directionalBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write p1=|c00|²+|c01|² and p2=|c00|²+|c10|². This is exactly V=p1²+p2²+2|c00 c11|²+2|c01 c10|². For a unit vector it also equals 2|c00|²+(|c01|²+|c10|²)². No real-phase restriction is imposed.

**Theorem 1.3 (Both-mode attenuation).**

$$\forall q \in \mathbb{R},\; 0 \le q \Rightarrow \left(q \le 1 \Rightarrow \left(\forall psi \in \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Prod}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right)\right),\; \operatorname{norm}\left(psi\right) = 1 \Rightarrow \operatorname{opNorm}\left(\operatorname{jumpMap}\left(\operatorname{modeJump}\left(0\right), q, \operatorname{jumpMap}\left(\operatorname{modeJump}\left(1\right), q, \operatorname{vecMulVec}\left(\operatorname{ofLp}\left(psi\right), \operatorname{star}\left(\operatorname{ofLp}\left(psi\right)\right)\right)\right)\right)\right) \le \operatorname{sub}\left(1, \operatorname{div}\left(\operatorname{mul}\left(\operatorname{mul}\left(q, \operatorname{sub}\left(1, q\right)\right), \operatorname{directionalBudget}\left(psi\right)\right), 2\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/TwistedTwoModeOUComparison.two_mode_pure_state_attenuation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each mode the generic theorem bounds norm(H_i(P)) by 1−q(1−q)(p_i−|c_i|²). Entrywise complex algebra and unit normalization prove the sum of these two defects is V. The two actual maps commute; positivity and unital Hermitian contraction therefore bound norm(H1(H2(P))) by each single-mode norm. Averaging yields the stated factor one half. opNorm means norm of Matrix.toEuclideanCLM. Parameter endpoints and arbitrary complex phases are included. The filtered no-jump estimate, full low-temperature tube and nonnegativity of G are not claimed here.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/TwistedTwoModeOUComparison.directionalBudget`
- Truth anchor: `D5/S3/Quantum/Semigroups/TwistedTwoModeOUComparison.modeJump`
- Truth anchor: `D5/S3/Quantum/Semigroups/TwistedTwoModeOUComparison.two_mode_pure_state_attenuation`
- Dependency: [D5/S3/Quantum/Foundation/TwoKrausRankOneAttenuation](../Foundation/TwoKrausRankOneAttenuation.md)

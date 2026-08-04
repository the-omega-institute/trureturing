# Zero-Orbit Congruence

## Abstract

Separate the finite congruence premise from the global norm exclusion in the 36-divisibility step.

This module records the exact finite-ring part of a local-to-global divisibility argument. The local candidate disjunction modulo 36 remains an explicit premise; no residue enumeration is inferred from the two theorems below.

<a id="describe-eisenstein-norm-mod-three"></a>

**Theorem 1.1 (Eisenstein norm residues modulo three).**

$\forall x,y \in \mathbb{Z}/3\mathbb{Z},\ x^{2}-xy+y^{2}=0 \lor x^{2}-xy+y^{2}=1$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/ZeroOrbitCongruence.eisenstein_norm_mod_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The norm polynomial x^2 - xy + y^2 takes only residues zero and one in Z/3Z. The proof exhausts all nine residue pairs.

<a id="describe-thirty-six-local-to-global"></a>

**Theorem 1.2 (The local candidates collapse to divisibility by 36).**

$$\forall m \in \mathbb{N},\ \forall x,y \in \mathbb{Z}/3\mathbb{Z},\ ((m \operatorname{mod} 36=0 \lor m \operatorname{mod} 36=8) \land ([m]_{3}=x^{2}-xy+y^{2})) \Rightarrow 36 \mid m$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/ZeroOrbitCongruence.thirty_six_dvd_of_local_candidates_and_eisenstein_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the local computation leaves residues zero and eight modulo 36, and the represented residue is an Eisenstein norm modulo three, the residue eight branch is impossible. The result does not prove the local 432-case computation that supplies the candidate disjunction.

## References

- Truth anchor: `D5/S1/Phase/ZeroOrbitCongruence.eisenstein_norm_mod_three`
- Truth anchor: `D5/S1/Phase/ZeroOrbitCongruence.thirty_six_dvd_of_local_candidates_and_eisenstein_norm`

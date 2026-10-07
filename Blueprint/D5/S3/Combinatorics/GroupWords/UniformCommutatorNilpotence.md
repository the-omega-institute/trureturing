# Uniform Commutator Words and Nilpotence

## Abstract

A uniform vanishing depth for commutator words of generators forces their generated subgroup to be nilpotent.

**Theorem 1.1 (From generators to the whole generated subgroup).**

$$\forall G \in Typeu,\; Group\left(G\right) \Rightarrow \left(\forall S \in Sets\left(G\right),\; \forall N \in Nat,\; vanish\left(G, S, N\right) \Rightarrow Nilpotent\left(Generated\left(G, S\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GroupWords/UniformCommutatorNilpotence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* FrenzyMath and upstream contributors (2026). *Poincare-Conjecture library prerequisites for hyperbolic rigidity*. URL: <https://github.com/frenzymath/Poincare-Conjecture/tree/432c38f2aa5a30efb13871292d17b4a3309a496a>.

*Commentary.*

G is any group in any type universe, S any subset of G, and N any natural number. The predicate vanish(G,S,N) means: for every list l of exactly N elements of S and every b in S, start at z=b and process the list from left to right, replacing z by a*z*a inverse*z inverse at each letter a. The final element is one. The same N works for every such list and root; a root-dependent or word-dependent depth is not sufficient.

Generated(G,S) is the actual subgroup closure of S with its induced group structure. Nilpotent means that its upper central series reaches the whole subgroup after finitely many steps. S need not be finite, symmetric, normal, or contain one. The empty set and N=0 remain in scope.

Work inside the generated subgroup H and pull S back through its inclusion to a set T generating all of H. Induct on n to show that a root annihilated by every length-n T word belongs to the nth upper central subgroup. At zero the empty word forces the root to be one. At a successor, prefix any generator a to a word: the induction hypothesis puts the commutator of a with the root into the preceding upper central subgroup.

In the quotient by that normal upper central subgroup, every generator therefore commutes with the root image. Pulling back the centralizer of that image gives a subgroup containing T, hence all of H. Thus the root commutes with every element modulo the preceding term and belongs to the next term. This promotes a condition on generators to the whole group; it does not assume that S is normal or closed under commutators.

Inclusion into G intertwines each commutator and the complete list fold. The stated uniform vanishing premise then puts every element of T into the Nth upper central subgroup. Since T generates H, that term is all of H, proving nilpotence. The premise itself must be established for any geometric application; this theorem does not supply a Lorentz matrix estimate, a hyperbolic deck representation, a Margulis bound, or rigidity.

## References

- Truth anchor: `D5/S3/Combinatorics/GroupWords/UniformCommutatorNilpotence.result`

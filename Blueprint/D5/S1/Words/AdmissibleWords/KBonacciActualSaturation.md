# Sharp saturation by actual binary words

## Abstract

The exact length needed to realize every binary single-probe residue is determined by the forbidden run length and the probe degree. Every zero occupies one position.

Fix natural numbers k and a with k at least two and a at least two. Let H be the quotient of the polynomial ring over ZMod 2 by the monic polynomial Phi_a = X^a minus the sum of X^j for j from zero through a-1. A word of length n is a function from Fin n to Bool; its jth bit is the coefficient of X^j. The set I_n consists exactly of the quotient classes of words accepted by the k-bonacci scanner, which forbids k consecutive true bits. This is the accepted image; it does not identify rejected words with accepted words.

Set N(k,a) equal to a when a is below k, and otherwise to the maximum of a+1 and 2a-2k+3. The quotient is the original monic polynomial quotient, with no irreducibility or squarefree assumption.

**Theorem 1.1 (The cardinality and all exact-length saturation thresholds).**

$$\operatorname{card}(H) = 2^{a} \land \forall n\in\mathbb{N}, (I_{n} = H \Leftrightarrow N(k,a) \leq n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/KBonacciActualSaturation.kbonacci_actual_saturation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The monic quotient has exactly 2^a elements. In characteristic two, Phi_a is the all-one polynomial of length b=a+1 and the residue of X has bth power one. Folding positions modulo b preserves the observation. Two folded binary vectors represent the same residue exactly when they coincide or are complements.

If a is below k, every length-a word is legal. If k is at most a and a is at most 2k-2, a vector of length a+1 or its complement is legal, since disjoint runs of k zeros and k ones cannot both fit. The length-a target with its first k bits equal to one has no legal representative.

For a at least 2k-1, put u=a+2-2k. Choose a complementary folded representative whose final block B of length 2k-1 is legal and does not have k-1 ones at both ends. The exceptional legal block with both ends full has a legal complement with zero ends. Split the length-u prefix by parity into E and F, orienting the split to put a zero at any critical join. The actual word EBF has length 2a-2k+3, is legal at both joins, and folds to the chosen representative.

One position below that length, the last 2k cyclic coordinates occur exactly once. The folded target with k final ones forces a run of k ones in either complementary representative. Appending actual high-end zeros preserves both legality and the quotient class, extending the upper bounds and all lower exclusions to every natural length, including zero.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/KBonacciActualSaturation.kbonacci_actual_saturation`
- Dependency: [D5/S0/Tower/DBonacci/Substitution](../../../S0/Tower/DBonacci/Substitution.md)

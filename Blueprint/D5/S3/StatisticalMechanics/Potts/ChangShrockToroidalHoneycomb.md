# An alternating vector for toroidal honeycomb strips

## Abstract

The labelled degree L-1 honeycomb transfer operator has eigenvalue v^(2(L-1))(v+q)^2 for every even L at least two.

**Definition 1.1 (Coeff).**

$$\operatorname{Coeff} = \operatorname{MvPolynomial}\left(\operatorname{Fin}\left(2\right), \mathbb{Z}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.Coeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

Coeff is the polynomial ring over the integers with two independent variables indexed by Fin 2.

**Definition 1.2 (q).**

$$\operatorname{q} = \operatorname{MvPolynomial}.\operatorname{X}\left(0\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

The first polynomial indeterminate is the Potts component weight q.

**Definition 1.3 (v).**

$$\operatorname{v} = \operatorname{MvPolynomial}.\operatorname{X}\left(1\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.v` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

The second polynomial indeterminate is the Potts bond weight v.

**Definition 1.4 (Adjacent).**

$$\forall (L: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(L\right)), (\forall (j: \operatorname{Fin}\left(L\right)), ((\operatorname{Adjacent}\left(i, j\right)) \Leftrightarrow ((\operatorname{Nat}.\operatorname{mod}\left((\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1), L\right) = \operatorname{Fin}.\operatorname{val}\left(j\right)) \lor (\operatorname{Nat}.\operatorname{mod}\left((\operatorname{Fin}.\operatorname{val}\left(j\right)) + (1), L\right) = \operatorname{Fin}.\operatorname{val}\left(i\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.Adjacent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

Sites are numbered from zero; mod denotes Nat.mod. Adjacency is symmetric and includes the cyclic seam.

**Definition 1.5 (Native).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \forall (f: (\operatorname{Fin}\left(L\right)) \to (\operatorname{Fin}\left(L\right))), ((\operatorname{Native}\left(L, f\right)) \Leftrightarrow ((\exists (s: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(L\right)\right)), (f = \operatorname{Equiv}.\operatorname{toFun}\left(s\right))) \lor (\exists (s: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(L\right)\right)), (\exists (i: \operatorname{Fin}\left(L\right)), (\exists (j: \operatorname{Fin}\left(L\right)), ((i \ne j) \land ((\operatorname{Adjacent}\left(i, j\right)) \land ((\operatorname{Equiv}.\operatorname{toFun}\left(s\right)\left(i\right) = 0) \land (f = \operatorname{Function}.\operatorname{update}\left(\operatorname{Equiv}.\operatorname{toFun}\left(s\right), i, \operatorname{Equiv}.\operatorname{toFun}\left(s\right)\left(j\right)\right)))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.Native` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

The nonzero symbols are the L-1 distinct marks. A bijective word represents singleton components, with symbol zero unmarked. The second alternative replaces the zero at i by the mark at its cyclic neighbor j. The two equal symbols then encode one marked double block. These are exactly the two possible block shapes with L sites and L-1 marked components. Nonadjacent double blocks separate marked sites on both sides and violate the annular noncrossing condition. For L=2 the seam has the same endpoints as the other bond. The bases (2.16) and (2.18) have respectively 3 and 48 labelled states.

**Definition 1.6 (State).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \operatorname{State}\left(L\right) = \{(f: (\operatorname{Fin}\left(L\right)) \to (\operatorname{Fin}\left(L\right))) \mid \operatorname{Native}\left(L, f\right)\})$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.State` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

State L retains the labelled connectivity word, with a proof that it is native. Equal words are the same diagram, including the two descriptions of a double block.

**Definition 1.7 (Space).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \operatorname{Space}\left(L\right) = \operatorname{Finsupp}\left(\operatorname{State}\left(L\right), \operatorname{Coeff}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.Space` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

Space L is the free module of polynomial coefficients on the native degree L-1 diagrams.

**Definition 1.8 (ket).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \forall (f: (\operatorname{Fin}\left(L\right)) \to (\operatorname{Fin}\left(L\right))), (\operatorname{ket}\left(f\right) = \operatorname{dite}\left(\operatorname{Native}\left(L, f\right), ((h: \operatorname{Native}\left(L, f\right)) \mapsto \operatorname{Finsupp}.\operatorname{single}\left(\operatorname{Subtype}.\operatorname{mk}\left(f, h\right), 1\right)), \operatorname{Function}.\operatorname{const}\left(\operatorname{Not}\left(\operatorname{Native}\left(L, f\right)\right), 0\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.ket` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

A native connectivity word gives its unit basis vector: dite binds h : Native L f, and Subtype.mk f h is the native state. A word outside this degree block gives zero.

**Definition 1.9 (join).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \forall (i: \operatorname{Fin}\left(L\right)), (\forall (j: \operatorname{Fin}\left(L\right)), (\operatorname{join}\left(i, j\right) = \operatorname{Finsupp}.\operatorname{linearCombination}\left(\operatorname{Coeff}, ((s: \operatorname{State}\left(L\right)) \mapsto \operatorname{ite}\left(\operatorname{Subtype}.\operatorname{val}\left(s\right)\left(i\right) = \operatorname{Subtype}.\operatorname{val}\left(s\right)\left(j\right), \operatorname{Finsupp}.\operatorname{single}\left(s, 1\right), \operatorname{ite}\left(\operatorname{Subtype}.\operatorname{val}\left(s\right)\left(i\right) = 0, \operatorname{ket}\left(\operatorname{Function}.\operatorname{update}\left(\operatorname{Subtype}.\operatorname{val}\left(s\right), i, \operatorname{Subtype}.\operatorname{val}\left(s\right)\left(j\right)\right)\right), \operatorname{ite}\left(\operatorname{Subtype}.\operatorname{val}\left(s\right)\left(j\right) = 0, \operatorname{ket}\left(\operatorname{Function}.\operatorname{update}\left(\operatorname{Subtype}.\operatorname{val}\left(s\right), j, \operatorname{Subtype}.\operatorname{val}\left(s\right)\left(i\right)\right)\right), 0\right)\right)\right))\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.join` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

Joining sites already in the same block changes nothing. An unmarked block takes the other block's mark when they merge. Two different marks cannot be identified. The linear extension is over Coeff; s denotes the underlying connectivity word.

**Definition 1.10 (detach).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \forall (i: \operatorname{Fin}\left(L\right)), (\operatorname{detach}\left(i\right) = \operatorname{Finsupp}.\operatorname{linearCombination}\left(\operatorname{Coeff}, ((s: \operatorname{State}\left(L\right)) \mapsto \operatorname{ite}\left(\operatorname{Subtype}.\operatorname{val}\left(s\right)\left(i\right) = 0, \operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{q}, \operatorname{Finsupp}.\operatorname{single}\left(s, 1\right)\right), \operatorname{ite}\left(\exists (j: \operatorname{Fin}\left(L\right)), ((j \ne i) \land (\operatorname{Subtype}.\operatorname{val}\left(s\right)\left(j\right) = \operatorname{Subtype}.\operatorname{val}\left(s\right)\left(i\right))), \operatorname{ket}\left(\operatorname{Function}.\operatorname{update}\left(\operatorname{Subtype}.\operatorname{val}\left(s\right), i, 0\right)\right), 0\right)\right))\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.detach` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

Closing the unmarked singleton multiplies by q. A site of a marked double block detaches to an unmarked singleton. Removing a marked singleton loses a bridge and therefore projects to zero in this block.

**Definition 1.11 (vertical).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \operatorname{vertical}\left(L\right) = \operatorname{List}.\operatorname{prod}\left(\operatorname{List}.\operatorname{ofFn}\left(((i: \operatorname{Fin}\left(L\right)) \mapsto (\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{v}, 1\right)) + (\operatorname{detach}\left(i\right)))\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.vertical` (`✓ std3`).

*Citation.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

This is the ordered longitudinal product V of equation (2.34). List.prod multiplies endomorphisms by composition, in increasing site order.

**Definition 1.12 (horizontal).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \forall (b: \operatorname{Bool}), (\operatorname{horizontal}\left(L, b\right) = \operatorname{List}.\operatorname{prod}\left(\operatorname{List}.\operatorname{ofFn}\left(((k: \operatorname{Fin}\left(\operatorname{Nat}.\operatorname{div}\left(L, 2\right)\right)) \mapsto (1) + (\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{v}, \operatorname{join}\left(\operatorname{Fin}.\operatorname{ofNat}\left(L, ((2) \cdot (\operatorname{Fin}.\operatorname{val}\left(k\right))) + (\operatorname{ite}\left(b, 1, 0\right))\right), \operatorname{Fin}.\operatorname{ofNat}\left(L, (((2) \cdot (\operatorname{Fin}.\operatorname{val}\left(k\right))) + (\operatorname{ite}\left(b, 1, 0\right))) + (1)\right)\right)\right)))\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.horizontal` (`✓ std3`).

*Citation.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

The Boolean b selects the second bond layer. Its offset is one when true and zero when false. For even L, false pairs sites 0-1, 2-3 and so on; true pairs sites 1-2, 3-4 and the seam L-1 to 0. Fin.ofNat reduces site numbers modulo L. Here Nat.div L 2 is the integer quotient floor(L/2). These are the two honeycomb H operators in equation (2.34).

**Definition 1.13 (transfer).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \operatorname{transfer}\left(L\right) = ((\operatorname{vertical}\left(L\right)) \cdot (\operatorname{horizontal}\left(L, \operatorname{true}\right))) \cdot ((\operatorname{vertical}\left(L\right)) \cdot (\operatorname{horizontal}\left(L, \operatorname{false}\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.transfer` (`✓ std3`).

*Citation.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

Equation (2.35) defines T=(V Htwo)(V Hone). The operator acts on the full native labelled degree L-1 block, including double-block states.

**Definition 1.14 (alternatingVector).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \operatorname{alternatingVector}\left(L\right) = \sum_{s \in \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(L\right)\right)} \operatorname{Finsupp}.\operatorname{single}\left(\operatorname{Subtype}.\operatorname{mk}\left(\operatorname{Equiv}.\operatorname{toFun}\left(s\right), \operatorname{Or}.\operatorname{inl}\left(\operatorname{Exists}.\operatorname{intro}\left(s, \operatorname{rfl}\right)\right)\right), (\operatorname{Int}.\operatorname{cast}\left(\operatorname{Units}.\operatorname{val}\left(\operatorname{Equiv}.\operatorname{Perm}.\operatorname{sign}\left(s\right)\right)\right): \operatorname{Coeff})\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.alternatingVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

Equiv.Perm.sign takes values in ℤˣ. Units.val gives its integer value, and Int.cast embeds it in Coeff. The basis state is the native singleton state Subtype.mk (Equiv.toFun s) (Or.inl (Exists.intro s rfl)); thus the formula uses exactly the native singleton state and Finsupp.single of the definition. The identity permutation contributes one; all other permutations give different labelled singleton diagrams.

**Theorem 1.15 (alternatingVector_ne_zero).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \operatorname{alternatingVector}\left(L\right) \ne 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.alternatingVector_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

The identity permutation has coefficient one in the alternating vector.

**Theorem 1.16 (join_alternating).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \forall (i: \operatorname{Fin}\left(L\right)), (\forall (j: \operatorname{Fin}\left(L\right)), ((i \ne j) \to (\operatorname{join}\left(i, j\right)\left(\operatorname{alternatingVector}\left(L\right)\right) = 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.join_alternating` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

For any two different sites, with no parity or adjacency restriction, pair each permutation with its product by their transposition. The join images agree and the integer signs are opposite.

**Theorem 1.17 (list_prod_on_vector).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \forall (A: \operatorname{Type}*), (\forall (xs: \operatorname{List}\left(A\right)), (\forall (B: (A) \to (\operatorname{Module}.\operatorname{End}\left(\operatorname{Coeff}, \operatorname{Space}\left(L\right)\right))), (\forall (c: (A) \to (\operatorname{Coeff})), (\forall (w: \operatorname{Space}\left(L\right)), ((\forall (a: A), ((a \in xs) \to (B\left(a\right)\left(w\right) = \operatorname{HSMul}.\operatorname{hSMul}\left(c\left(a\right), w\right)))) \to (\operatorname{List}.\operatorname{prod}\left(\operatorname{List}.\operatorname{map}\left(B, xs\right)\right)\left(w\right) = \operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{List}.\operatorname{prod}\left(\operatorname{List}.\operatorname{map}\left(c, xs\right)\right), w\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.list_prod_on_vector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

The list retains its order. The hypothesis specifies the action of every factor on w; scalar linearity gives the product action. The type A is arbitrary, including types in any universe.

**Theorem 1.18 (vertical_alternating).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \operatorname{vertical}\left(L\right)\left(\operatorname{alternatingVector}\left(L\right)\right) = \operatorname{HSMul}.\operatorname{hSMul}\left(((\operatorname{v})^{((L) - (1))}) \cdot ((\operatorname{v}) + (\operatorname{q})), \operatorname{alternatingVector}\left(L\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.vertical_alternating` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

Every nonzero width is allowed. Each permutation has exactly one zero symbol, giving the factor v+q; its other L-1 sites each give v.

**Theorem 1.19 (The eigenvalue at every even width).**

$$\forall (L: \mathbb{N}), ((2 \le L) \to ((\operatorname{Even}\left(L\right)) \to (\exists (w: \operatorname{Space}\left(L\right)), ((w \ne 0) \land (\operatorname{transfer}\left(L\right)\left(w\right) = \operatorname{HSMul}.\operatorname{hSMul}\left(((\operatorname{v})^{((2) \cdot ((L) - (1)))}) \cdot (((\operatorname{v}) + (\operatorname{q}))^{(2)}), w\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.result` (`✓ std3`). ∎

*Resolves.* `Problems/changshrock2005honeycomb` (proved) by `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"changshrock2005honeycomb","declaration_gid":"D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

Let w be the alternating singleton vector. For two distinct adjacent sites, interchange their symbols. The permutation sign reverses. If both symbols are marks, the join is zero. If one is zero, both arrangements give the same marked double block. Consequently the join contributions cancel in pairs, including across the cyclic seam, so each transverse layer fixes w.

On any singleton arrangement, detaching a marked site is zero and detaching the unique unmarked site contributes q. The longitudinal product therefore multiplies every such basis vector by v^(L-1)(v+q). Applying the two longitudinal layers and the two transverse layers gives v^(2(L-1))(v+q)^2 times w. The identity coefficient proves w is nonzero over the polynomial ring itself; no division by v or specialization of q is used.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.Adjacent`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.Coeff`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.Native`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.Space`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.State`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.alternatingVector`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.alternatingVector_ne_zero`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.detach`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.horizontal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.join`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.join_alternating`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.ket`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.list_prod_on_vector`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.q`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.result`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.transfer`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.v`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.vertical`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.vertical_alternating`

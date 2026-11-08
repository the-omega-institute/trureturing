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

$$\operatorname{q} = \operatorname{MvPolynomialX}\left(0\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

MvPolynomialX denotes MvPolynomial.X. The first polynomial indeterminate is the Potts component weight q.

**Definition 1.3 (v).**

$$\operatorname{v} = \operatorname{MvPolynomialX}\left(1\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.v` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

The second polynomial indeterminate is the Potts bond weight v.

**Definition 1.4 (Adjacent).**

$$\forall (L: \mathbb{N}), (\forall (i: \operatorname{Fin}\left(L\right)), (\forall (j: \operatorname{Fin}\left(L\right)), ((\operatorname{Adjacent}\left(i, j\right)) \Leftrightarrow ((\operatorname{mod}\left((\operatorname{val}\left(i\right)) + (1), L\right) = \operatorname{val}\left(j\right)) \lor (\operatorname{mod}\left((\operatorname{val}\left(j\right)) + (1), L\right) = \operatorname{val}\left(i\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.Adjacent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

Sites are numbered from zero. Adjacency is symmetric and includes the cyclic seam.

**Definition 1.5 (Native).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \forall (f: (\operatorname{Fin}\left(L\right)) \to (\operatorname{Fin}\left(L\right))), ((\operatorname{Native}\left(L, f\right)) \Leftrightarrow ((\exists (s: \operatorname{Perm}\left(\operatorname{Fin}\left(L\right)\right)), (f = s)) \lor (\exists (s: \operatorname{Perm}\left(\operatorname{Fin}\left(L\right)\right)), (\exists (i: \operatorname{Fin}\left(L\right)), (\exists (j: \operatorname{Fin}\left(L\right)), ((i \ne j) \land ((\operatorname{Adjacent}\left(i, j\right)) \land ((s\left(i\right) = 0) \land (f = \operatorname{update}\left(s, i, s\left(j\right)\right)))))))))))$$

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

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \forall (f: (\operatorname{Fin}\left(L\right)) \to (\operatorname{Fin}\left(L\right))), (\operatorname{ket}\left(f\right) = \operatorname{ite}\left(\operatorname{Native}\left(L, f\right), \operatorname{single}\left(\operatorname{subtype}\left(f\right), 1\right), 0\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.ket` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

A native connectivity word gives its unit basis vector. A word outside this degree block gives zero; the subtype proof carries no extra state information.

**Definition 1.9 (join).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \forall (i: \operatorname{Fin}\left(L\right)), (\forall (j: \operatorname{Fin}\left(L\right)), (\operatorname{join}\left(i, j\right) = \operatorname{linearCombination}\left(\operatorname{Coeff}, ((s: \operatorname{State}\left(L\right)) \mapsto \operatorname{ite}\left(s\left(i\right) = s\left(j\right), \operatorname{single}\left(s, 1\right), \operatorname{ite}\left(s\left(i\right) = 0, \operatorname{ket}\left(\operatorname{update}\left(s, i, s\left(j\right)\right)\right), \operatorname{ite}\left(s\left(j\right) = 0, \operatorname{ket}\left(\operatorname{update}\left(s, j, s\left(i\right)\right)\right), 0\right)\right)\right))\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.join` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

Joining sites already in the same block changes nothing. An unmarked block takes the other block's mark when they merge. Two different marks cannot be identified. The linear extension is over Coeff; s denotes the underlying connectivity word.

**Definition 1.10 (detach).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \forall (i: \operatorname{Fin}\left(L\right)), (\operatorname{detach}\left(i\right) = \operatorname{linearCombination}\left(\operatorname{Coeff}, ((s: \operatorname{State}\left(L\right)) \mapsto \operatorname{ite}\left(s\left(i\right) = 0, (\operatorname{q}) \cdot (\operatorname{single}\left(s, 1\right)), \operatorname{ite}\left(\exists (j: \operatorname{Fin}\left(L\right)), ((j \ne i) \land (s\left(j\right) = s\left(i\right))), \operatorname{ket}\left(\operatorname{update}\left(s, i, 0\right)\right), 0\right)\right))\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.detach` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

Closing the unmarked singleton multiplies by q. A site of a marked double block detaches to an unmarked singleton. Removing a marked singleton loses a bridge and therefore projects to zero in this block.

**Definition 1.11 (vertical).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \operatorname{vertical}\left(L\right) = \operatorname{ListProd}\left(\operatorname{ofFn}\left(((i: \operatorname{Fin}\left(L\right)) \mapsto ((\operatorname{v}) \cdot (1)) + (\operatorname{detach}\left(i\right)))\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.vertical` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

This is the ordered longitudinal product V of equation (2.34). ListProd multiplies endomorphisms by composition, in increasing site order.

**Definition 1.12 (horizontal).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \forall (b: \operatorname{Bool}), (\operatorname{horizontal}\left(L, b\right) = \operatorname{ListProd}\left(\operatorname{ofFn}\left(((k: \operatorname{Fin}\left(\operatorname{div}\left(L, 2\right)\right)) \mapsto (1) + ((\operatorname{v}) \cdot (\operatorname{join}\left(\operatorname{ofNat}\left(L, ((2) \cdot (\operatorname{val}\left(k\right))) + (\operatorname{ite}\left(b, 1, 0\right))\right), \operatorname{ofNat}\left(L, (((2) \cdot (\operatorname{val}\left(k\right))) + (\operatorname{ite}\left(b, 1, 0\right))) + (1)\right)\right))))\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.horizontal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

The Boolean b selects the second bond layer. Its offset is one when true and zero when false. Thus false pairs sites 0-1, 2-3 and so on; true pairs sites 1-2, 3-4 and the seam L-1 to 0. Fin.ofNat reduces site numbers modulo L. These are the two honeycomb H operators in equation (2.34).

**Definition 1.13 (transfer).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \operatorname{transfer}\left(L\right) = ((\operatorname{vertical}\left(L\right)) \cdot (\operatorname{horizontal}\left(L, \operatorname{true}\right))) \cdot ((\operatorname{vertical}\left(L\right)) \cdot (\operatorname{horizontal}\left(L, \operatorname{false}\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.transfer` (`✓ std3`).

*Citation.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

Equation (2.35) defines T=(V Htwo)(V Hone). The operator acts on the full native labelled degree L-1 block, including double-block states.

**Definition 1.14 (alternatingVector).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \operatorname{alternatingVector}\left(L\right) = \sum_{s \in \operatorname{Perm}\left(\operatorname{Fin}\left(L\right)\right)} \operatorname{single}\left(\operatorname{subtype}\left(s\right), \operatorname{IntCast}\left(\operatorname{PermSign}\left(s\right)\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.alternatingVector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

PermSign denotes Equiv.Perm.sign followed by coercion to the integers; IntCast embeds that integer into Coeff. The sum runs over all permutations of the L symbols. Its singleton-state coefficient is the integer sign, embedded in Coeff. The identity permutation contributes coefficient one, and no other permutation represents that labelled singleton diagram.

**Theorem 1.15 (The eigenvalue at every even width).**

$$\forall (L: \mathbb{N}), ((2 \le L) \to ((\operatorname{Even}\left(L\right)) \to (\exists (w: \operatorname{Space}\left(L\right)), ((w \ne 0) \land (\operatorname{transfer}\left(L\right)\left(w\right) = ((\operatorname{v})^{((2) \cdot ((L) - (1)))}) \cdot ((((\operatorname{v}) + (\operatorname{q}))^{(2)}) \cdot (w)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.result` (`✓ std3`). ∎

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
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.detach`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.horizontal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.join`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.ket`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.q`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.result`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.transfer`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.v`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb.vertical`

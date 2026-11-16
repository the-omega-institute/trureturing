# An alternating vector for toroidal square strips

## Abstract

Every native toroidal square degree L-1 block has eigenvalue v^(L-1)(v+q).

The coefficient ring, native labelled states, join and detach maps, vertical operator and alternating vector are those of D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalHoneycomb. In the formulas their original declaration names retain that namespace. Coeff is MvPolynomial (Fin 2) ℤ; q and v are respectively MvPolynomial.X 0 and MvPolynomial.X 1. Space L is State L →₀ Coeff. All products act by composition of Coeff-linear endomorphisms.

**Definition 1.1 (All cyclic bonds).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \operatorname{horizontal}\left(L\right) = \operatorname{List}.\operatorname{prod}\left(\operatorname{List}.\operatorname{ofFn}\left(((i: \operatorname{Fin}\left(L\right)) \mapsto (1) + (\operatorname{HSMul}.\operatorname{hSMul}\left(\operatorname{v}, \operatorname{join}\left(i, \operatorname{Fin}.\operatorname{ofNat}\left(L, (\operatorname{Fin}.\operatorname{val}\left(i\right)) + (1)\right)\right)\right)))\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalSquare.horizontal` (`✓ std3`).

*Citation.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

This is H in equation (2.34). The function bound by List.ofFn has domain Fin L and codomain Module.End Coeff (Space L). Its 1 is the identity endomorphism. HSMul.hSMul is scalar multiplication, and Fin.val is the explicit coercion of a site to ℕ. Fin.ofNat L n has value Nat.mod n L, the nonnegative remainder. Thus the last factor joins L-1 to 0. List.prod retains increasing site order and all L factors. At L=2 the two endpoint pairs are reversed descriptions of the same bond; both factors are retained. Nat.div is natural quotient division; no quotient or half-width convention enters this H.

**Definition 1.2 (The square transfer map).**

$$\forall (L: \mathbb{N}), ([\operatorname{NeZero}\left(L\right)] \operatorname{transfer}\left(L\right) = (\operatorname{vertical}\left(L\right)) \cdot (\operatorname{horizontal}\left(L\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalSquare.transfer` (`✓ std3`).

*Citation.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

Equation (2.35) gives T=VH. Multiplication in Module.End is composition, so H acts first. The reused vertical operator is literally List.prod (List.ofFn (fun i : Fin L => v • 1 + detach i)). The operators act on the full native labelled degree L-1 space, including adjacent marked double blocks.

**Theorem 1.3 (The eigenvalue at every width).**

$$\forall (L: \mathbb{N}), ((2 \le L) \to (\exists (w: \operatorname{Space}\left(L\right)), ((w \ne 0) \land (\operatorname{transfer}\left(L\right)\left(w\right) = \operatorname{HSMul}.\operatorname{hSMul}\left(((\operatorname{v})^{((L) - (1))}) \cdot ((\operatorname{v}) + (\operatorname{q})), w\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalSquare.result` (`✓ std3`). ∎

*Resolves.* `Problems/changshrock2005square` (proved) by `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalSquare.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"changshrock2005square","declaration_gid":"D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalSquare.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Shu-Chiuan Chang and Robert Shrock (2005). *Transfer Matrices for the Partition Function of the Potts Model on Toroidal Lattice Strips*. DOI: [10.1016/j.physa.2005.08.076](https://doi.org/10.1016/j.physa.2005.08.076). URL: <https://arxiv.org/abs/cond-mat/0506274v1>.

*Commentary.*

The premise 2 ≤ L supplies the local NeZero L instance in the Lean statement. Natural subtraction L-1 is therefore ordinary predecessor subtraction. The witness is the original alternatingVector L. Its identity-permutation coefficient is one, so alternatingVector_ne_zero supplies nonzeroness over ℤ[q,v].

For every i : Fin L, i differs from Fin.ofNat L (i.val+1): away from the seam their values differ by one; at the seam the values are L-1 and zero. The owner theorem join_alternating therefore annihilates the witness at every cyclic bond, for odd and even L alike. Every factor of H fixes it. Applying the owner list_prod_on_vector with constant scalar one proves H fixes it, including both factors at width two.

The owner theorem vertical_alternating gives Vw=v^(L-1)(v+q) • w. Together with H w=w this proves the displayed statement. Equation (5.18) expresses the corresponding Tutte eigenvalue x; equation (5.21) gives precisely this Potts form. The polynomial theorem uses no division or specialization. It makes no claim about amplitudes or the second eigenvalue y.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalSquare.horizontal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalSquare.result`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalSquare.transfer`
- Dependency: [D5/S3/StatisticalMechanics/Potts/ChangShrockToroidalHoneycomb](ChangShrockToroidalHoneycomb.md)

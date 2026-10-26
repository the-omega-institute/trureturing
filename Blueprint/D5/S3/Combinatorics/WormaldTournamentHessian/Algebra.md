# Tournament Hessian: algebra

## Abstract

Regular tournament Hessians: algebra.

**Theorem 1.1 (The skew diagonal vanishes).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \forall i \in \operatorname {Fin}\left(d\right),\; \operatorname {skewAdjacency}\left(A, i, i\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.skewDiag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting a matrix from its transpose cancels the diagonal. This identifies the diagonal of each shifted matrix.

**Theorem 1.2 (Skew entries are bounded by one).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \forall i \in \operatorname {Fin}\left(d\right),\; \forall j \in \operatorname {Fin}\left(d\right),\; \operatorname {Norm.norm}\left(\operatorname {Int.castRingHom}\left(\mathbb {C}\right)\left(\operatorname {skewAdjacency}\left(A, i, j\right)\right)\right) \le 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.skewNormLe` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A difference of Boolean adjacency entries is −1, zero or one. Its complex norm is at most one.

**Theorem 1.3 (Strict diagonal dominance).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; \forall c \in \mathbb {C},\; (\operatorname {Norm.norm}\left(c\right) = d) \Rightarrow (\operatorname {Matrix.det}\left(\operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) + c\cdot (1)\right) \ne 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.shiftedDetNeZero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal has norm d and the sum of the other entry norms in each row is at most d−1. Gershgorin's strict diagonal-dominance consequence gives a nonzero determinant. No tournament or parity assumption is needed.

**Theorem 1.4 (The imaginary shift in odd dimension).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (\operatorname {Odd}\left(d\right)) \Rightarrow (\operatorname {Complex.re}\left(\operatorname {Matrix.det}\left(\operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) + \operatorname {Complex.I} \cdot d\cdot (1)\right)\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.shiftedDetPureImaginary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shifted matrix is skew Hermitian. Conjugating its determinant multiplies it by −1 in odd dimension, so the real part vanishes.

**Theorem 1.5 (The imaginary determinant has integral coefficient).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (\operatorname {Odd}\left(d\right)) \Rightarrow (\exists b \in \mathbb {Z},\; \operatorname {Matrix.det}\left(\operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) + \operatorname {Complex.I} \cdot d\cdot (1)\right) = \operatorname {Int.cast}\left(b\right) \cdot \operatorname {Complex.I})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.imaginaryShiftIntegral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every entry of the imaginary shift is a Gaussian integer. Its determinant is a Gaussian integer with real part zero, and therefore equals bi for an integer b.

**Theorem 1.6 (The determinant quotient is rational).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (\operatorname {Odd}\left(d\right)) \Rightarrow (\exists q \in \mathbb {Q},\; (q \ne 0) \land (\frac{\operatorname {Matrix.det}\left(d\cdot (1) + \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)}{\frac{\operatorname {Matrix.det}\left(\operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) + \operatorname {Complex.I} \cdot d\cdot (1)\right)}{\operatorname {Complex.I}}} = \operatorname {Rat.cast}\left(q\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.algebraicRatioRational` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real shift is an integral matrix. The imaginary-shift determinant divided by i is also an integer. Strict diagonal dominance makes both integers nonzero; their quotient supplies a nonzero rational.

**Theorem 1.7 (A quotient of quadratic determinants is a rational square).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (\operatorname {Odd}\left(d\right)) \Rightarrow (\exists q \in \mathbb {Q},\; (q \ne 0) \land (\frac{\operatorname {Matrix.det}\left(d^{2}\cdot (1) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) \cdot \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)}{\operatorname {Matrix.det}\left(d^{2}\cdot (1) + \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) \cdot \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)} = \operatorname {Rat.cast}\left(q\right)^{2}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.algebraicSquareIdentity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Transposition identifies the determinants of dI+S and dI−S. Factoring d²I−S² gives the square of the first determinant. Factoring d²I+S² and using odd dimension gives the square of det(S+idI)/i. Thus the quotient is the square of the previously constructed rational. The theorem calH_closedForm identifies this quotient with d divided by the analytic Hessian determinant.

**Theorem 1.8 (The algebraic square for regular tournaments).**

$$\forall d \in \mathbb {N},\; \forall A \in \operatorname {Fin}\left(d\right) \to \left(\operatorname {Fin}\left(d\right) \to Bool\right),\; (3 \le d) \Rightarrow ((\operatorname {IsRegularTournament}\left(A\right)) \Rightarrow (\exists q \in \mathbb {Q},\; (q \ne 0) \land (\frac{\operatorname {Matrix.det}\left(d^{2}\cdot (1) - \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) \cdot \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)}{\operatorname {Matrix.det}\left(d^{2}\cdot (1) + \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right) \cdot \operatorname {Matrix.map}\left(\operatorname {skewAdjacency}\left(A\right), \operatorname {Int.castRingHom}\left(\mathbb {C}\right)\right)\right)} = \operatorname {Rat.cast}\left(q\right)^{2})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.regularAlgebraicSquare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Oddness of a regular tournament supplies the hypothesis of the quadratic determinant identity. The theorem calH_closedForm supplies the analytic identification, and regularLocalSolution supplies the required existence.

## Matrix identities and inverse variations

**Theorem 1.9 (The determinant of the difference-and-constant basis).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \operatorname {Matrix.det}\left(\operatorname {bridgeU}\right) = \operatorname {Nat.cast}\left(\operatorname {Fintype.card}\left(iota\right)\right) + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.bridgeU_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix with identity upper-left block, an all-one final column and an all-minus-one final row has determinant card(iota)+1, by its scalar Schur complement.

**Theorem 1.10 (Difference-basis columns).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall i \in \operatorname {Sum}\left(iota, Unit\right),\; \forall j \in iota,\; \operatorname {bridgeU}\left(i, \operatorname {Sum.inl}\left(j\right)\right) = \operatorname {ite}\left(i = \operatorname {Sum.inl}\left(j\right), 1, 0\right) - \operatorname {ite}\left(i = \operatorname {Sum.inr}\left(\operatorname {Unit.unit}\right), 1, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.bridgeU_entry_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each initial column is the corresponding coordinate vector minus the final coordinate vector.

**Theorem 1.11 (The constant-basis column).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall i \in \operatorname {Sum}\left(iota, Unit\right),\; \operatorname {bridgeU}\left(i, \operatorname {Sum.inr}\left(\operatorname {Unit.unit}\right)\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.bridgeU_entry_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The final column of the basis matrix is the constant vector one.

**Theorem 1.12 (The block diagonal congruence).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall T \in \operatorname {Matrix}\left(\operatorname {Sum}\left(iota, Unit\right), \operatorname {Sum}\left(iota, Unit\right), \mathbb {C}\right),\; (\forall i \in \operatorname {Sum}\left(iota, Unit\right),\; \sum_{l: \operatorname {Sum}\left(iota, Unit\right)} T\left(i, l\right) = 0 - 1) \Rightarrow ((\forall j \in \operatorname {Sum}\left(iota, Unit\right),\; \sum_{l: \operatorname {Sum}\left(iota, Unit\right)} T\left(l, j\right) = 0 - 1) \Rightarrow (\operatorname {Matrix.transpose}\left(\operatorname {bridgeU}\right) \cdot T \cdot \operatorname {bridgeU} = \operatorname {Matrix.fromBlocks}\left(\operatorname {bridgeH}\left(T\right), 0, 0, \operatorname {Matrix.of}\left((i: Unit\mapsto (k: Unit\mapsto 0 - \left(\operatorname {Nat.cast}\left(\operatorname {Fintype.card}\left(iota\right)\right) + 1\right)))\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.bridgeU_congr` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every row and column sums to minus one, congruence by the difference-and-constant basis has vanishing off-diagonal blocks, difference minor in the initial block and final entry minus (card(iota)+1).

**Theorem 1.13 (The determinant of the difference minor).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall T \in \operatorname {Matrix}\left(\operatorname {Sum}\left(iota, Unit\right), \operatorname {Sum}\left(iota, Unit\right), \mathbb {C}\right),\; (\forall i \in \operatorname {Sum}\left(iota, Unit\right),\; \sum_{l: \operatorname {Sum}\left(iota, Unit\right)} T\left(i, l\right) = 0 - 1) \Rightarrow ((\forall j \in \operatorname {Sum}\left(iota, Unit\right),\; \sum_{l: \operatorname {Sum}\left(iota, Unit\right)} T\left(l, j\right) = 0 - 1) \Rightarrow (\operatorname {Matrix.det}\left(\operatorname {bridgeH}\left(T\right)\right) = \left(0 - \left(\operatorname {Nat.cast}\left(\operatorname {Fintype.card}\left(iota\right)\right) + 1\right)\right) \cdot \operatorname {Matrix.det}\left(T\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.bridge_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking determinants of the block congruence and cancelling the nonzero basis determinant gives det(H)=−(card(iota)+1)det(T).

**Theorem 1.14 (The determinant of the symmetric resolvent expression).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall c \in \mathbb {C},\; (\operatorname {Matrix.transpose}\left(S\right) = 0 - S) \Rightarrow ((\operatorname {Odd}\left(\operatorname {Fintype.card}\left(iota\right)\right)) \Rightarrow ((\operatorname {Matrix.det}\left(c\cdot (1) - S\right) \ne 0) \Rightarrow (\operatorname {Matrix.det}\left(1 - c\cdot (\operatorname {Inv.inv}\left(c\cdot (1) - S\right) + \operatorname {Matrix.transpose}\left(\operatorname {Inv.inv}\left(c\cdot (1) - S\right)\right))\right) = \frac{0 - \operatorname {Matrix.det}\left(c^{2}\cdot (1) + S \cdot S\right)}{\operatorname {Matrix.det}\left(c^{2}\cdot (1) - S \cdot S\right)})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.skew_resolvent_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying T by (cI−S)(cI+S) gives −(c²I+S²). Transposition gives invertibility of both factors. Taking determinants in odd dimension yields the negative quadratic determinant quotient.

**Theorem 1.15 (The finite-coordinate difference determinant).**

$$\forall n \in \mathbb {N},\; \forall T \in \operatorname {Matrix}\left(\operatorname {Fin}\left(n + 1\right), \operatorname {Fin}\left(n + 1\right), \mathbb {C}\right),\; (\forall i \in \operatorname {Fin}\left(n + 1\right),\; \sum_{l: \operatorname {Fin}\left(n + 1\right)} T\left(i, l\right) = 0 - 1) \Rightarrow ((\forall j \in \operatorname {Fin}\left(n + 1\right),\; \sum_{l: \operatorname {Fin}\left(n + 1\right)} T\left(l, j\right) = 0 - 1) \Rightarrow (\operatorname {Matrix.det}\left(\operatorname {Matrix.of}\left((i: \operatorname {Fin}\left(n\right)\mapsto (k: \operatorname {Fin}\left(n\right)\mapsto T\left(\operatorname {Fin.castSucc}\left(i\right), \operatorname {Fin.castSucc}\left(k\right)\right) - T\left(\operatorname {Fin.castSucc}\left(i\right), \operatorname {Fin.last}\left(n\right)\right) - T\left(\operatorname {Fin.last}\left(n\right), \operatorname {Fin.castSucc}\left(k\right)\right) + T\left(\operatorname {Fin.last}\left(n\right), \operatorname {Fin.last}\left(n\right)\right)))\right)\right) = \left(0 - \left(\operatorname {Nat.cast}\left(n\right) + 1\right)\right) \cdot \operatorname {Matrix.det}\left(T\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.differenceMinor_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reindexing the difference-minor identity onto Fin(n+1) gives the determinant formula with multiplier −(n+1).

**Theorem 1.16 (Constant row sums of the inverse).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall Q \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall c \in \mathbb {C},\; (c \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(Q\right) \ne 0) \Rightarrow ((\forall i \in iota,\; \sum_{l: iota} Q\left(i, l\right) = c) \Rightarrow (\forall i \in iota,\; \sum_{l: iota} \operatorname {Inv.inv}\left(Q\right)\left(i, l\right) = \operatorname {Inv.inv}\left(c\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.inverse_row_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If Q maps the constant vector one to c times that vector, its inverse maps one to c inverse times one.

**Theorem 1.17 (Constant column sums of the inverse).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall Q \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall c \in \mathbb {C},\; (c \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(Q\right) \ne 0) \Rightarrow ((\forall j \in iota,\; \sum_{l: iota} Q\left(l, j\right) = c) \Rightarrow (\forall j \in iota,\; \sum_{l: iota} \operatorname {Inv.inv}\left(Q\right)\left(l, j\right) = \operatorname {Inv.inv}\left(c\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.inverse_col_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the row-sum identity to the transpose gives the corresponding column sums of the inverse.

**Theorem 1.18 (The resolvent expression has sums minus one).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall Q \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall c \in \mathbb {C},\; (c \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(Q\right) \ne 0) \Rightarrow ((\forall i \in iota,\; \sum_{l: iota} Q\left(i, l\right) = c) \Rightarrow ((\forall j \in iota,\; \sum_{l: iota} Q\left(l, j\right) = c) \Rightarrow ((\forall i \in iota,\; \sum_{l: iota} \left(1 - c\cdot (\operatorname {Inv.inv}\left(Q\right) + \operatorname {Matrix.transpose}\left(\operatorname {Inv.inv}\left(Q\right)\right))\right)\left(i, l\right) = 0 - 1) \land (\forall j \in iota,\; \sum_{l: iota} \left(1 - c\cdot (\operatorname {Inv.inv}\left(Q\right) + \operatorname {Matrix.transpose}\left(\operatorname {Inv.inv}\left(Q\right)\right))\right)\left(l, j\right) = 0 - 1)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.resolvent_row_col_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two inverse sums each contribute c inverse. Subtracting c times their sum from the identity leaves row and column sums equal to minus one.

**Theorem 1.19 (The determinant quotient for the difference minor).**

$$\forall n \in \mathbb {N},\; \forall S \in \operatorname {Matrix}\left(\operatorname {Fin}\left(n + 1\right), \operatorname {Fin}\left(n + 1\right), \mathbb {C}\right),\; \forall c \in \mathbb {C},\; (c \ne 0) \Rightarrow ((\operatorname {Matrix.transpose}\left(S\right) = 0 - S) \Rightarrow ((\operatorname {Odd}\left(n + 1\right)) \Rightarrow ((\operatorname {Matrix.det}\left(c\cdot (1) - S\right) \ne 0) \Rightarrow ((\forall i \in \operatorname {Fin}\left(n + 1\right),\; \sum_{l: \operatorname {Fin}\left(n + 1\right)} S\left(i, l\right) = 0) \Rightarrow (\operatorname {Matrix.det}\left(\operatorname {Matrix.of}\left((i: \operatorname {Fin}\left(n\right)\mapsto (k: \operatorname {Fin}\left(n\right)\mapsto \left(1 - c\cdot (\operatorname {Inv.inv}\left(c\cdot (1) - S\right) + \operatorname {Matrix.transpose}\left(\operatorname {Inv.inv}\left(c\cdot (1) - S\right)\right))\right)\left(\operatorname {Fin.castSucc}\left(i\right), \operatorname {Fin.castSucc}\left(k\right)\right) - \left(1 - c\cdot (\operatorname {Inv.inv}\left(c\cdot (1) - S\right) + \operatorname {Matrix.transpose}\left(\operatorname {Inv.inv}\left(c\cdot (1) - S\right)\right))\right)\left(\operatorname {Fin.castSucc}\left(i\right), \operatorname {Fin.last}\left(n\right)\right) - \left(1 - c\cdot (\operatorname {Inv.inv}\left(c\cdot (1) - S\right) + \operatorname {Matrix.transpose}\left(\operatorname {Inv.inv}\left(c\cdot (1) - S\right)\right))\right)\left(\operatorname {Fin.last}\left(n\right), \operatorname {Fin.castSucc}\left(k\right)\right) + \left(1 - c\cdot (\operatorname {Inv.inv}\left(c\cdot (1) - S\right) + \operatorname {Matrix.transpose}\left(\operatorname {Inv.inv}\left(c\cdot (1) - S\right)\right))\right)\left(\operatorname {Fin.last}\left(n\right), \operatorname {Fin.last}\left(n\right)\right)))\right)\right) = \frac{\left(\operatorname {Nat.cast}\left(n\right) + 1\right) \cdot \operatorname {Matrix.det}\left(c^{2}\cdot (1) + S \cdot S\right)}{\operatorname {Matrix.det}\left(c^{2}\cdot (1) - S \cdot S\right)})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.skew_difference_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero row sums of a skew matrix also give zero column sums. The resolvent expression therefore has sums minus one, and its difference-minor determinant is (n+1)det(c²I+S²)/det(c²I−S²).

**Theorem 1.20 (Differentiating matrix inversion).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall Q \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; (\operatorname {Matrix.det}\left(Q\right) \ne 0) \Rightarrow (\operatorname {HasFDerivAt}\left(\mathbb {C}, (M: \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right)\mapsto \operatorname {Inv.inv}\left(M\right)), 0 - \operatorname {ContinuousLinearMap.mulLeftRight}\left(\mathbb {C}, \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right), \operatorname {Inv.inv}\left(Q\right), \operatorname {Inv.inv}\left(Q\right)\right), Q\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.matrixInverse_hasFDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an invertible complex matrix Q, the derivative of inversion maps H to −Q inverse H Q inverse. The matrix operator norm permits direct application of the normed-algebra inverse theorem.

**Theorem 1.21 (Differentiating the diagonal resolvent).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow (\operatorname {HasFDerivAt}\left(\mathbb {C}, \operatorname {inverseQ}\left(S\right), \operatorname {inverseQDeriv}\left(y\right), y\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.inverseQ_hasFDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each diagonal entry 2/y_j has derivative −2v_j/y_j². The off-diagonal skew matrix is constant.

**Theorem 1.22 (Differentiating the inverse resolvent).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, y\right)\right) \ne 0) \Rightarrow (\operatorname {HasFDerivAt}\left(\mathbb {C}, (u: iota \to \mathbb {C}\mapsto \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, u\right)\right)), \operatorname {ContinuousLinearMap.comp}\left(0 - \operatorname {ContinuousLinearMap.mulLeftRight}\left(\mathbb {C}, \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right), \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right), \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\right), \operatorname {inverseQDeriv}\left(y\right)\right), y\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.inverse_hasFDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The chain rule composes the diagonal resolvent derivative with the derivative of matrix inversion.

**Theorem 1.23 (Differentiating the inverse-entry sum).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, y\right)\right) \ne 0) \Rightarrow (\operatorname {HasFDerivAt}\left(\mathbb {C}, \operatorname {alpha}\left(S\right), \operatorname {ContinuousLinearMap.comp}\left(\operatorname {sumEntriesCLM}, \operatorname {ContinuousLinearMap.comp}\left(0 - \operatorname {ContinuousLinearMap.mulLeftRight}\left(\mathbb {C}, \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right), \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right), \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\right), \operatorname {inverseQDeriv}\left(y\right)\right)\right), y\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.alpha_hasFDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing all matrix entries is a continuous linear functional, so its composition with the inverse resolvent has the indicated derivative.

**Theorem 1.24 (Smoothness of the diagonal resolvent).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow (\operatorname {ContDiffAt}\left(\mathbb {C}, 2, \operatorname {inverseQ}\left(S\right), y\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.inverseQ_contDiffAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonzero coordinate hypothesis makes each reciprocal coordinate complex C2. Diagonal embedding and subtraction preserve this regularity.

**Theorem 1.25 (Smoothness of the inverse resolvent).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, y\right)\right) \ne 0) \Rightarrow (\operatorname {ContDiffAt}\left(\mathbb {C}, 2, (u: iota \to \mathbb {C}\mapsto \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, u\right)\right)), y\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.inverse_contDiffAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inversion is analytic on the units of a complex normed algebra. The nonzero determinant hypothesis allows composition with the C2 diagonal resolvent.

**Theorem 1.26 (Smoothness of the scalar inverse-entry equation).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, y\right)\right) \ne 0) \Rightarrow (\operatorname {ContDiffAt}\left(\mathbb {C}, 2, \operatorname {alpha}\left(S\right), y\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.alpha_contDiffAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of inverse entries is complex C2 wherever all coordinates and the resolvent determinant are nonzero.

**Theorem 1.27 (A single-coordinate diagonal derivative).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall y \in iota \to \mathbb {C},\; \forall j \in iota,\; \operatorname {inverseQDeriv}\left(y\right)\left(\operatorname {Pi.single}\left(j, 1\right)\right) = \frac{0 - 2}{y\left(j\right)^{2}}\cdot (\operatorname {Matrix.diagonal}\left(\operatorname {Pi.single}\left(j, 1\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.inverseQDeriv_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating the diagonal resolvent derivative on a coordinate vector gives a diagonal matrix supported at that coordinate.

**Theorem 1.28 (A single-coordinate inverse derivative).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, y\right)\right) \ne 0) \Rightarrow (\forall j \in iota,\; \operatorname {fderiv}\left(\mathbb {C}, (u: iota \to \mathbb {C}\mapsto \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, u\right)\right)), y, \operatorname {Pi.single}\left(j, 1\right)\right) = \frac{2}{y\left(j\right)^{2}}\cdot (\operatorname {Matrix.of}\left((i: iota\mapsto (k: iota\mapsto \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(i, j\right) \cdot \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(j, k\right)))\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.inverse_fderiv_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The jth partial derivative of the inverse matrix is 2/y_j² times the outer product of its jth column and jth row.

**Theorem 1.29 (Differentiating an inverse row sum).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, y\right)\right) \ne 0) \Rightarrow (\forall j \in iota,\; \forall k \in iota,\; \operatorname {fderiv}\left(\mathbb {C}, (u: iota \to \mathbb {C}\mapsto \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, u\right)\right)\left(j, l\right)), y, \operatorname {Pi.single}\left(k, 1\right)\right) = \frac{2}{y\left(k\right)^{2}} \cdot \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(j, k\right) \cdot \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(k, l\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.row_fderiv_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the single-coordinate inverse derivative across a row gives 2V_jk/y_k² times the kth inverse row sum.

**Theorem 1.30 (Differentiating an inverse column sum).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, y\right)\right) \ne 0) \Rightarrow (\forall j \in iota,\; \forall k \in iota,\; \operatorname {fderiv}\left(\mathbb {C}, (u: iota \to \mathbb {C}\mapsto \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, u\right)\right)\left(l, j\right)), y, \operatorname {Pi.single}\left(k, 1\right)\right) = \frac{2}{y\left(k\right)^{2}} \cdot \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(k, j\right) \cdot \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(l, k\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.col_fderiv_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing the single-coordinate inverse derivative down a column gives 2V_kj/y_k² times the kth inverse column sum.

**Theorem 1.31 (First partials of the scalar inverse-entry equation).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, y\right)\right) \ne 0) \Rightarrow (\forall j \in iota,\; \operatorname {fderiv}\left(\mathbb {C}, \operatorname {alpha}\left(S\right), y, \operatorname {Pi.single}\left(j, 1\right)\right) = \frac{2}{y\left(j\right)^{2}} \cdot \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(j, l\right) \cdot \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(l, j\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.alpha_fderiv_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first partial is 2/y_j² times the product of the jth inverse row and column sums.

**Theorem 1.32 (The derivative of a reciprocal square).**

$$\forall t \in \mathbb {C},\; (t \ne 0) \Rightarrow (\operatorname {HasDerivAt}\left(\mathbb {C}, (u: \mathbb {C}\mapsto \frac{2}{u^{2}}), \frac{0 - 4}{t^{3}}, t\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.inverse_square_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scalar function 2/t² has derivative −4/t³ at every nonzero complex number.

**Theorem 1.33 (Second partials of the scalar inverse-entry equation).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; (\forall i \in iota,\; y\left(i\right) \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, y\right)\right) \ne 0) \Rightarrow (\forall j \in iota,\; \forall k \in iota,\; \operatorname {fderiv}\left(\mathbb {C}, (u: iota \to \mathbb {C}\mapsto \operatorname {fderiv}\left(\mathbb {C}, \operatorname {alpha}\left(S\right), u, \operatorname {Pi.single}\left(j, 1\right)\right)), y, \operatorname {Pi.single}\left(k, 1\right)\right) = \frac{0 - 4}{y\left(j\right)^{3}} \cdot \operatorname {ite}\left(k = j, 1, 0\right) \cdot \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(j, l\right) \cdot \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(l, j\right) + \frac{4}{y\left(j\right)^{2} \cdot y\left(k\right)^{2}} \cdot \left(\operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(j, k\right) \cdot \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(k, l\right) \cdot \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(l, j\right) + \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(k, j\right) \cdot \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(j, l\right) \cdot \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(l, k\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.alpha_second_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first-partial formula holds on a neighbourhood where coordinates and determinant remain nonzero. Differentiating that equality uses the reciprocal-square derivative and the inverse row and column derivatives, producing the displayed second partial.

**Theorem 1.34 (Equal first partials at a balanced constant point).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall b \in \mathbb {C},\; (b \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, \operatorname {Function.const}\left(iota, b\right)\right)\right) \ne 0) \Rightarrow ((\forall i \in iota,\; \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, \operatorname {Function.const}\left(iota, b\right)\right)\right)\left(i, l\right) = \frac{b}{2}) \Rightarrow ((\forall j \in iota,\; \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, \operatorname {Function.const}\left(iota, b\right)\right)\right)\left(l, j\right) = \frac{b}{2}) \Rightarrow (\forall j \in iota,\; \operatorname {fderiv}\left(\mathbb {C}, \operatorname {alpha}\left(S\right), \operatorname {Function.const}\left(iota, b\right), \operatorname {Pi.single}\left(j, 1\right)\right) = \frac{1}{2}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.alpha_first_const` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When all coordinates equal b and every inverse row and column sums to b/2, every first partial equals one half.

**Theorem 1.35 (The second-partial matrix at a balanced constant point).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall b \in \mathbb {C},\; (b \ne 0) \Rightarrow ((\operatorname {Matrix.det}\left(\operatorname {inverseQ}\left(S, \operatorname {Function.const}\left(iota, b\right)\right)\right) \ne 0) \Rightarrow ((\forall i \in iota,\; \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, \operatorname {Function.const}\left(iota, b\right)\right)\right)\left(i, l\right) = \frac{b}{2}) \Rightarrow ((\forall j \in iota,\; \sum_{l: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, \operatorname {Function.const}\left(iota, b\right)\right)\right)\left(l, j\right) = \frac{b}{2}) \Rightarrow (\forall j \in iota,\; \forall k \in iota,\; \operatorname {fderiv}\left(\mathbb {C}, (u: iota \to \mathbb {C}\mapsto \operatorname {fderiv}\left(\mathbb {C}, \operatorname {alpha}\left(S\right), u, \operatorname {Pi.single}\left(j, 1\right)\right)), \operatorname {Function.const}\left(iota, b\right), \operatorname {Pi.single}\left(k, 1\right)\right) = \operatorname {Inv.inv}\left(b^{2}\right) \cdot \left(\operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, \operatorname {Function.const}\left(iota, b\right)\right)\right)\left(j, k\right) + \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, \operatorname {Function.const}\left(iota, b\right)\right)\right)\left(k, j\right)\right) - \operatorname {ite}\left(j = k, \operatorname {Inv.inv}\left(b\right), 0\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.alpha_second_const` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the balanced constant point, the second-partial matrix is b inverse squared times V plus its transpose, minus b inverse times the identity.

**Definition 1.36 (The diagonal resolvent).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; \operatorname {inverseQ}\left(S, y\right) = \operatorname {Matrix.diagonal}\left((j: iota\mapsto \frac{2}{y\left(j\right)})\right) - S$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.inverseQ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal matrix with entries 2/y_j minus S.

**Definition 1.37 (The inverse-entry sum).**

$$\forall iota \in Type,\; [\operatorname {Fintype}\left(iota\right)] [\operatorname {DecidableEq}\left(iota\right)] \forall S \in \operatorname {Matrix}\left(iota, iota, \mathbb {C}\right),\; \forall y \in iota \to \mathbb {C},\; \operatorname {alpha}\left(S, y\right) = \sum_{i: iota} \sum_{j: iota} \operatorname {Inv.inv}\left(\operatorname {inverseQ}\left(S, y\right)\right)\left(i, j\right)$$

*Formalization.* `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.alpha` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum of all entries of the matrix inverse of inverseQ.

## References

- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.algebraicRatioRational`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.algebraicSquareIdentity`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.alpha`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.alpha_contDiffAt`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.alpha_fderiv_single`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.alpha_first_const`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.alpha_hasFDerivAt`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.alpha_second_const`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.alpha_second_single`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.bridgeU_congr`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.bridgeU_det`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.bridgeU_entry_left`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.bridgeU_entry_right`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.bridge_det`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.col_fderiv_single`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.differenceMinor_det`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.imaginaryShiftIntegral`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.inverseQ`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.inverseQDeriv_single`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.inverseQ_contDiffAt`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.inverseQ_hasFDerivAt`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.inverse_col_sum`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.inverse_contDiffAt`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.inverse_fderiv_single`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.inverse_hasFDerivAt`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.inverse_row_sum`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.inverse_square_hasDerivAt`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.matrixInverse_hasFDerivAt`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.regularAlgebraicSquare`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.resolvent_row_col_sum`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.row_fderiv_single`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.shiftedDetNeZero`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.shiftedDetPureImaginary`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.skewDiag`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.skewNormLe`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.skew_difference_det`
- Truth anchor: `D5/S3/Combinatorics/WormaldTournamentHessian/Algebra.skew_resolvent_det`
- Dependency: [D5/S3/Combinatorics/WormaldTournamentHessian/Defs](Defs.md)

# A conserved comparison for three emission values

## Abstract

Three real emission values admit one conserved reversible comparison with the same stationary row and simultaneous displacement and total-variation bounds.

Let J={0,1,2}. All table entries and emission parameters are arbitrary real numbers. The probability row pi is strictly positive and sums to one. The matrix B is nonnegative, each row sums to one, and pi(i)B(i,j)=pi(j)B(j,i). Both u and v belong to the closed interval [1/3,2/5] at every label. The original second update matrix is the identity and its intermediate row is pi.

StationaryTable is the existing finite stationary-table structure. In the formula, piOf(T) is its probability row and C(T) its stochastic matrix. identity(J)(i,j) is one when i=j and zero otherwise. Every sum is over the displayed finite label set J. The energy expression is J(u)=(1/2) sum_i sum_j pi(i)B(i,j)(u(i)-u(j))^2. The comparison uses the same pi, keeps v unchanged, and keeps the second update equal to the identity.

**Theorem 1.1 (One table satisfies every bound for every positive threshold).**

$$\forall pi:J\to Real,\forall B:J\to J\to Real,\forall u:J\to Real,\forall v:J\to Real,\forall t:Real,((\forall i:J,0<pi(i))\land(\sum_{i\in J} {pi(i)}=1)\land(\forall i:J,\forall j:J,0\le B(i,j))\land(\forall i:J,\sum_{j\in J} {B(i,j)}=1)\land(\forall i:J,\forall j:J,pi(i)\cdot B(i,j)=pi(j)\cdot B(j,i))\land(\forall i:J,(\frac{1}{3}\le u(i))\land(u(i)\le \frac{2}{5}))\land(\forall i:J,(\frac{1}{3}\le v(i))\land(v(i)\le \frac{2}{5}))\land(0<t))\Rightarrow \exists T:StationaryTable(J),\exists w:J\to Real,\exists Ah:J\to J\to Real,\exists vh:J\to Real,\exists tauh:J\to Real,(piOf(T)=pi)\land(Ah=identity(J))\land(vh=v)\land(tauh=pi)\land(\forall i:J,(\frac{1}{3}\le w(i))\land(w(i)\le \frac{2}{5}))\land(\forall i:J,(\frac{1}{3}\le vh(i))\land(vh(i)\le \frac{2}{5}))\land(\forall i:J,\forall j:J,0\le C(T)(i,j))\land(\forall i:J,\sum_{j\in J} {C(T)(i,j)}=1)\land(\forall i:J,\forall j:J,pi(i)\cdot C(T)(i,j)=pi(j)\cdot C(T)(j,i))\land(\forall j:J,\sum_{i\in J} {pi(i)\cdot C(T)(i,j)}=pi(j))\land(\forall i:J,\forall j:J,0<C(T)(i,j)\Rightarrow w(i)=w(j))\land(\sum_{i\in J} {pi(i)\cdot \lvert u(i)-w(i)\rvert }\le t)\land(\sum_{i\in J} {pi(i)\cdot \frac{1}{2}\cdot \sum_{j\in J} {\lvert B(i,j)-C(T)(i,j)\rvert }}\le \frac{2\cdot \frac{1}{2}\cdot \sum_{i\in J} {\sum_{j\in J} {pi(i)\cdot B(i,j)\cdot (u(i)-u(j))^{2}}}}{(t)^{2}})\land(\frac{1}{2}\cdot \sum_{i\in J} {\sum_{j\in J} {pi(i)\cdot C(T)(i,j)\cdot (w(i)-w(j))^{2}}}=0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ThreeValueConservedComparison.three_value_conserved_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sort the three emission values, including ties, and cut precisely at adjacent gaps greater than t. Each resulting block contains at most two uncut gaps, so its span is at most 2t. Replace every emission in a block by the midpoint of its smallest and largest values. The midpoint stays in [1/3,2/5], and each label moves by at most t. Any two labels assigned different midpoints have original separation at least t.

For each row i, remove transitions to labels with a different new emission value and add their total mass to the diagonal entry. All retained off-diagonal entries remain unchanged. Nonnegativity and the row sum are preserved. Detailed balance is inherited within each new-emission class; between classes both directions vanish. Summing detailed balance against a stochastic row proves that the stationary row remains exactly pi.

Write l(i) for the removed mass in row i. The diagonal gains l(i), the deleted coordinates lose total mass l(i), and the remaining coordinates do not change. Therefore q(i)=(1/2) sum_j |B(i,j)-C(T)(i,j)| equals l(i). Every deleted edge has squared original emission separation at least t^2. Multiplication by its nonnegative flow pi(i)B(i,j) and summation gives t^2 sum_i pi(i)q(i) at most 2J(u). Dividing by the positive t^2 gives the stated bound. This estimate and the displacement bound refer to the same constructed table.

Every positive comparison edge joins equal new emissions. Every summand of its emission energy is consequently zero. The construction includes tied emissions, both closed endpoints, arbitrary positive weights, self-loops, disconnected and reducible chains, and heterogeneous v. It assumes no irreducibility, spectral gap, aperiodicity, or lower bound on the positive weights.

The comparison is an existence statement about mathematical tables. It supplies no physical implementation, sampling algorithm, observation interface, full-law distance estimate, or history-risk transport theorem.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ThreeValueConservedComparison.three_value_conserved_comparison`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ConstantSuspensionSeparator](ConstantSuspensionSeparator.md)

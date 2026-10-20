# Uniform Schmidt defect moment mechanism

## Abstract

Singular-safe PSD row bounds and exact independent finite-assignment moments.

The statements concern supplied real matrices and exact averages over all permutations. They provide a reusable matrix-family mechanism for a Schmidt-test application. They do not derive that matrix family from an actual APPT spectrum or from product corners and unitaries. The general assignment theorem assumes r at least three; the singleton top pool at r equal to two requires a separate argument.

**Definition 1.1 (Row sum).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.rowSum`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.rowSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite type I, real matrix K indexed by I on both axes, and i in I, rowSum(K,i) is the sum over j in I of K(i,j). The finite type may be empty.

**Definition 1.2 (Uniform quadratic charge).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.uniformCharge`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.uniformCharge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite type I and real matrix K on I, uniformCharge(K) is the sum over i in I of rowSum(K,i). It equals the quadratic form of K at the all-ones vector. There is no division or normalization in this definition.

**Definition 1.3 (Centered row energy).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.centeredRowEnergy`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.centeredRowEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite type I and real matrix K on I, let n be the cardinality of I and q=uniformCharge(K). Then centeredRowEnergy(K) is the sum over i in I of (rowSum(K,i)-q/n)^2, with real division as in Lean. The bounds below explicitly require I nonempty.

**Theorem 1.4 (Trace bound for a singular PSD matrix).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.centered_row_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.centered_row_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonempty finite type I and every real positive semidefinite matrix K on I, put n=card(I) and q=uniformCharge(K). Then centeredRowEnergy(K) <= q*(trace(K)-q/n). Positive definiteness and q>0 are not premises. In particular, q=0 and singular PSD matrices remain in scope. The PSD bilinear Cauchy-Schwarz inequality at a coordinate vector and the all-ones vector gives rowSum(K,i)^2 <= K(i,i)*q. Sum these inequalities and subtract q^2/n using the exact centered-energy expansion.

**Theorem 1.5 (Sign-sensitive bound without an inverse).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.centered_row_moment_of_nonpositive_offDiag`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.centered_row_moment_of_nonpositive_offDiag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonempty finite type I, every real positive semidefinite matrix K on I and every real gamma, assume K(i,j)<=0 whenever i differs from j and K(i,i)<=2*gamma for every i. With n=card(I) and q=uniformCharge(K), centeredRowEnergy(K) <= 4*gamma*q-q^2/n. No strict sign or nonsingularity is required. Compare the quadratic forms at x and at the coordinatewise absolute value of x; the off-diagonal signs and PSD imply x^T K x <= 4*gamma*sum x_i^2. PSD Cauchy-Schwarz then bounds the squared norm of Kx by 4*gamma times x^T K x. Cancellation treats zero energy separately and never divides by q. Apply this at the all-ones vector and center.

**Definition 1.6 (Uniform permutation average).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.permutationAverage`

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.permutationAverage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite type I and function f from permutations of I to the reals, permutationAverage(f) is the sum of f over all permutations divided by the cardinality of that permutation type. This is the exact uniform average, including all permutations and repeated pool values; the permutation type is nonempty even when I is empty.

**Theorem 1.7 (Exact second moment of a centered pool).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.permutation_weighted_second_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.permutation_weighted_second_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite type I with n=card(I)>=2 and every real functions z,w on I with sum z_i=0, the exact permutation average of (sum_i w_i*z_(pi(i)))^2 equals (sum_i z_i^2)/(n*(n-1)) times (n*sum_i w_i^2-(sum_i w_i)^2). There are no distinctness, strict positivity or nonzero variance premises. Permutation invariance gives the same diagonal moment at every slot and the same pair moment at every ordered pair of distinct slots. Summing a centered row derives the negative pair covariance. Expanding the weighted square and inserting both moments yields the formula.

**Theorem 1.8 (General-r independent assignment bound).**

Lean statement: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.general_r_assignment_moment`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.general_r_assignment_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let r,a,b be natural numbers with r>=3, a>=2 and b>=2. Let top:Fin(a)->Real and bottom:Fin(b)->Real be arbitrary pools. Supply a real r by r matrix K(pi,sigma) for every permutation pi of Fin(a) and every independently chosen permutation sigma of Fin(b). Supply real weights T_i(k) on Fin(r) by Fin(a), real weights B_i(k) on Fin(r) by Fin(b), a diagonal slot map d:Fin(r)->Fin(b), and real s,gamma. Write A=sum top, C=sum bottom, alpha=A/a, beta=C/b, VT=sum(top_i-alpha)^2 and VB=sum(bottom_i-beta)^2. Under all the conditions stated below, ((r-1)/(r+1))*VT+VB <= 4*s*min(C/(r+1),gamma)-2*s^2/r. Natural dimensions are cast to reals in these formulas. No ordering or nonnegativity of the individual pool entries is assumed.

The complete dimension and weight conditions are a=r*(r-1)/2 and b=r*(r+1)/2 as real identities, a>0, b>0, a-1 nonzero and b-1 nonzero. For every row i, sum_k T_i(k)=-(r-1), sum_k B_i(k)=r+1, (a*sum_k T_i(k)^2-(sum_k T_i(k))^2)/(a*(a-1))=2*(r-1)/(r*(r+1)), and (b*sum_k B_i(k)^2-(sum_k B_i(k))^2)/(b*(b-1))=2/r. These identities are premises of the abstract theorem; no incidence construction is inferred from their names.

The complete matrix and mean conditions hold for every pi,sigma and every row i: rowSum(K(pi,sigma),i)=sum_k T_i(k)*top(pi(k))+sum_k B_i(k)*bottom(sigma(k)); uniformCharge(K(pi,sigma))=2*s; trace(K(pi,sigma))=2*sum_i bottom(sigma(d(i))); K(pi,sigma) is positive semidefinite; its off-diagonal entries are nonpositive and its diagonal entries are at most 2*gamma. Finally C-A=s and -(r-1)*alpha+(r+1)*beta=2*s/r. In particular, PSD is supplied for the whole independently assigned family, rather than just one matrix or a correlated subset of assignments.

Center each pool at its own mean. The exact single-pool formula gives each row's top contribution 2*(r-1)*VT/(r*(r+1)) and bottom contribution 2*VB/r. Independent averaging removes the mixed term, including zero-variance fibers. Summing rows gives average centeredRowEnergy(K)=2*(r-1)*VT/(r+1)+2*VB. The trace averages to 2*r*C/b. Average the trace bound and the sign-sensitive bound over the same matrix family; use the b-cardinality identity and divide by two. PSD at the all-ones vector derives s>=0. This permits the two upper bounds to combine as the displayed minimum.

The actual-spectrum application still needs one construction from the original ordered APPT spectrum that supplies every independently permuted K, proves its product-corner or unitary realization, and derives PSD, signs, diagonal cap, the trace and row identities, the weight identities, and both defect/mean identities on that same spectrum. This bridge is not a premise renamed as APPT. At r=2 the top pool has cardinality one, so its centered variance is zero but the n>=2 permutation formula cannot be applied to that pool; a singleton argument must replace that step before the corresponding moment can be claimed. No full APPT theorem, physical attainment, optimal purity or equality classification is asserted here.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.centeredRowEnergy`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.centered_row_moment`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.centered_row_moment_of_nonpositive_offDiag`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.general_r_assignment_moment`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.permutationAverage`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.permutation_weighted_second_moment`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.rowSum`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/UniformSchmidtDefectMoment.uniformCharge`

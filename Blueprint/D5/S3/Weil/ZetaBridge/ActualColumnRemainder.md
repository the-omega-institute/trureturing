# Actual Weighted Column Remainder

## Abstract

SOURCE_ONLY_UNCOMPILED: faithful author statements; no validated provenance claim.

The actual weighted first-jet error and infinite paired remainder are owned here. All Lean proofs, Reg selections and Scribe emission await caller-owned verification.

**Definition 1.1 (The actual weighted absolute head moment).**

$$\operatorname{W}(S, v)=\operatorname{SumAbsIndexTimesCoefficientNorm}(S, v)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualColumnRemainder.weightedHeadMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

SOURCE_ONLY_UNCOMPILED. W(S,v)=sum_{n in S} abs(n)*norm(v(n)). S is any finite integer set and v has arbitrary complex values; the n=0 contribution is exactly zero. W is never replaced by A times the unweighted mass.

**Definition 1.2 (The exact paired weighted remainder budget).**

$$\operatorname{R}(c, N, A, S, v)=\operatorname{div}(\operatorname{mul}(8, \operatorname{square}(\operatorname{arithmeticBoundaryBudget}(c)), \operatorname{square}(\operatorname{W}(S, v)), \operatorname{square}(\operatorname{add}(N, 1))), \operatorname{mul}(3, \operatorname{square}(pi), \operatorname{cube}(N), \operatorname{square}(\operatorname{sub}(\operatorname{add}(N, 1), A))))$$

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualColumnRemainder.pairedRemainderBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

SOURCE_ONLY_UNCOMPILED. R=8*arithmeticBoundaryBudget(c)^2*W(S,v)^2*(M+1)^2/(3*pi^2*M^3*(M+1-A)^2). Its admitted domain is c>=2, natural M>0, real A>=0, abs(n)<=A for every n in S, and A<M+1. No stronger separation such as M>=2A is used.

**Theorem 1.3 (Weighted error of the actual divided-difference column).**

$$\operatorname{And}(\operatorname{AtLeastTwo}(c), \operatorname{Nonnegative}(A), \operatorname{HeadWithin}(S, A), \operatorname{Less}(A, \operatorname{abs}(m)))\Rightarrow\operatorname{LessEqual}(\operatorname{norm}(\operatorname{ColumnMinusJet}(c, S, v, m)), \operatorname{div}(\operatorname{mul}(2, \operatorname{arithmeticBoundaryBudget}(c), \operatorname{W}(S, v)), \operatorname{mul}(pi, \operatorname{abs}(m), \operatorname{sub}(\operatorname{abs}(m), A))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualColumnRemainder.weighted_coupling_first_jet_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SOURCE_ONLY_UNCOMPILED. For c>=2, every finite S subset Z, arbitrary v:Z->C, A>=0, abs(n)<=A on S, and integer m with A<abs(m), norm(couplingColumn(c,S,v,m)-couplingFirstJet(c,S,v,m))<=2*arithmeticBoundaryBudget(c)*W(S,v)/(pi*abs(m)*(abs(m)-A)). The proof consumes arithmetic_coupling_first_jet_error at each singleton with radius abs(n), including n=0, compares the positive denominators, and sums the actual differences. It imposes no reality or moment-vanishing premise.

**Theorem 1.4 (Infinite paired first-jet remainder with cubic cutoff decay).**

$$\operatorname{And}(\operatorname{AtLeastTwo}(c), \operatorname{Positive}(N), \operatorname{Nonnegative}(A), \operatorname{HeadWithin}(S, A), \operatorname{Less}(A, \operatorname{add}(N, 1)))\Rightarrow\operatorname{And}(\operatorname{Summable}(\operatorname{PairedRemainderSequence}(c, N, S, v)), \operatorname{LessEqual}(\operatorname{PairedRemainderTsum}(c, N, S, v), \operatorname{R}(c, N, A, S, v)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualColumnRemainder.paired_first_jet_remainder_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SOURCE_ONLY_UNCOMPILED. For every c>=2, natural M>0, real A>=0 with A<M+1 and abs(n)<=A on any finite integer S, and every complex coefficient function v, the sequence norm(Column(m)-Jet(m))^2+norm(Column(-m)-Jet(-m))^2, m=M+j+1, is summable and its genuine tsum is at most R. For t>=M+1, t/(t-A)<=(M+1)/(M+1-A); the one-sign square is bounded by C^2/t^4 with C=2*B*W*(M+1)/(pi*(M+1-A)). The consumed exact owner inverse-fourth partial tail yields 2*C^2/(3*M^3)=R. Both signs and the zero/empty head remain. For fixed head, c and A this budget has cubic cutoff decay. No finite terminal exterior cutoff is asserted.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualColumnRemainder.pairedRemainderBudget`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualColumnRemainder.paired_first_jet_remainder_tail`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualColumnRemainder.weightedHeadMass`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualColumnRemainder.weighted_coupling_first_jet_error`
- Dependency: [D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet](WeilArithmeticCouplingJet.md)
- Dependency: [D5/S3/Weil/ZetaBridge/WeilEvenFourierObservationTail](WeilEvenFourierObservationTail.md)

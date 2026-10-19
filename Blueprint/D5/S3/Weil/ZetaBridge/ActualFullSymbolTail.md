# Actual Full Arithmetic Symbol Tail

## Abstract

SOURCE_ONLY_UNCOMPILED: faithful author statements; no validated provenance claim.

All new Lean bodies, imported T2/T3 attempts, this Scribe DSL, and Reg registrations await actual caller-owned verification.

**Definition 1.1 (The actual finite first-moment constant).**

$$\operatorname{K}(c)=\operatorname{PhaseDenominatorSum}(c)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualFullSymbolTail.primeFirstMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

K(c)=sum_{q in Ico(2,c)} 2*abs(primeWeight(q))/norm(1-primePhase(c,q)). Every integer in the range is present, hence all prime powers; no phase-spacing premise is supplied. For c=2 this is the empty sum.

**Definition 1.2 (The refined full-symbol budget).**

$$\operatorname{B}(c, N)=\operatorname{T3tailBudget}(c, N)+\operatorname{div}(\operatorname{square}(\operatorname{E}(c, N)), N)+\operatorname{div}(2 \operatorname{K}(c) \operatorname{E}(c, N+1), \operatorname{square}(N+1))$$

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualFullSymbolTail.fullSymbolTailBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B(c,N)=PrimeSymbolResonance.tailBudget(c,N)+E(c,N)^2/N+2*K(c)*E(c,N+1)/(N+1)^2. Here the owner's sharpened finite envelope is E(c,m)=min(2+U(c)/m,pi/4+(U(c)+3/(4*a(c)))/m), with a=2*pi/log(c) and U=2*(cosh(log(c)/2)-1)/a. The full-tail Lean source and its public signatures are unchanged. T3 is the unchanged, uncompiled source attempt. The factor two comes from the actual A=H-S square. For fixed c>=2 the candidate envelope tends to pi/4; the smooth-square contribution then has leading coefficient pi^2/16 in 1/N, and its contribution after the existing paired factor 2/pi^2 has coefficient 1/8 multiplying norm(beta)^2/N. These limit interpretations still require real verification, are not asserted as new Lean limit theorems, and do not remove the prime tail, either moment, or the mixed term. This finite tail improvement proves no RH, Robin inequality, strict positivity, full column remainder or physical operator identification.

**Theorem 1.3 (Every actual prime first-moment block).**

$$\operatorname{AtLeastTwo}(c)\Rightarrow\operatorname{abs}(\operatorname{PrimeBlock}(c, M, k))\leq\operatorname{K}(c)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualFullSymbolTail.prime_first_moment_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2, any integer start M and any natural length k, abs(sum_{j<k} S(c,M+j))<=K(c), including k=0. The complex imaginary-part representation and geometric_block_norm are the existing T2 statements. Its actual phase lies strictly between angles zero and 2*pi, proving phase!=1 for each included q.

**Theorem 1.4 (Signed finite mixed tail with the refined minimum).**

$$\operatorname{AtLeastTwo}(c)\Rightarrow\operatorname{abs}(\operatorname{FiniteMixed}(c, N, k))\leq\operatorname{div}(\operatorname{K}(c) \operatorname{E}(c, N+1), \operatorname{square}(N+1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualFullSymbolTail.signed_mixed_partial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2, any natural N and any natural k, FiniteMixed is sum_{j<k} S_m*(A_m+S_m)/m^2, m=N+j+1. The proof applies the existing signed finite_abel_majorant twice at D=0,C=K, to x=S and x=-S, with the actual nonnegative antitone weight. The complete finite boundary term remains accounted for; no boundary limit is assumed.

**Theorem 1.5 (Absolute convergence followed by actual mixed tsum passage).**

$$\operatorname{AtLeastTwo}(c)\land\operatorname{Positive}(N)\Rightarrow\operatorname{AbsolutelySummable}(\operatorname{MixedSequence}(c, N))\land\operatorname{abs}(\operatorname{MixedTsum}(c, N))\leq\operatorname{div}(\operatorname{K}(c) \operatorname{E}(c, N+1), \operatorname{square}(N+1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualFullSymbolTail.signed_mixed_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2 and N>0, sum_j abs(S_m*(A_m+S_m)/m^2) converges and abs(tsum_j S_m*(A_m+S_m)/m^2)<=K(c)*E(c,N+1)/(N+1)^2, m=N+j+1. Absolute summability uses the finite sum of absolute prime weights times E(c,N) and the existing inverse-square summability. Only then does HasSum.tendsto_sum_nat pass the finite signed bound to the actual tsum.

**Theorem 1.6 (The complete actual symbol square tail).**

$$\operatorname{AtLeastTwo}(c)\land\operatorname{Positive}(N)\Rightarrow\operatorname{Summable}(\operatorname{FullEnergySequence}(c, N, beta))\land\operatorname{FullEnergyTsum}(c, N, beta)\leq\operatorname{normSq}(beta) \operatorname{B}(c, N)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualFullSymbolTail.full_symbol_square_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>=2, N>0 and arbitrary complex beta, the nonnegative sequence norm(beta*A(c,N+j+1)/(N+j+1))^2 is summable and its actual tsum is <=norm(beta)^2*B(c,N). A is exactly arithmeticBoundarySymbol. The proof sums A^2=S^2+H^2-2*S*H using established convergence of all three terms, and pays twice the absolute signed mixed estimate. There is no reality, vanishing, positivity or spacing hypothesis.

**Theorem 1.7 (Both exterior signs with both retained head moments).**

$$\operatorname{AtLeastTwo}(c)\land\operatorname{Positive}(N)\Rightarrow\operatorname{Summable}(\operatorname{PairedJetSequence}(c, N, S, v))\land\operatorname{PairedJetTsum}(c, N, S, v)\leq\operatorname{div}(2, \operatorname{square}(pi)) {\operatorname{div}(\operatorname{normSq}(alpha), N)+\operatorname{normSq}(beta) \operatorname{B}(c, N)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualFullSymbolTail.paired_first_jet_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite integer S and complex v, alpha=sum_{n in S} A(c,n)*v(n) and beta=sum_{n in S} v(n). The summed sequence is norm(couplingFirstJet(m))^2+norm(couplingFirstJet(-m))^2, m=N+j+1. It is summable and bounded by (2/pi^2)*(norm(alpha)^2/N+norm(beta)^2*B(c,N)). Native arithmetic_boundary_symbol_neg is reused and the private complex parallelogram calculation is consumed here. This paired enumeration includes both exterior signs. A literal tsum over an integer subtype is not asserted. The physical operator bridge and column remainder remain separate.

**Definition 1.8 (Both complex first-jet moments retained).**

$$\operatorname{J}(c, N, S, v)=\operatorname{mul}(\operatorname{div}(2, \operatorname{square}(pi)), \operatorname{add}(\operatorname{div}(\operatorname{normSq}(alpha), N), \operatorname{mul}(\operatorname{normSq}(beta), \operatorname{fullSymbolTailBudget}(c, N))))$$

*Formalization.* `D5/S3/Weil/ZetaBridge/ActualFullSymbolTail.pairedJetBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

SOURCE_ONLY_UNCOMPILED. J=(2/pi^2)*(norm(alpha)^2/M+norm(beta)^2*fullSymbolTailBudget(c,M)), alpha=sum A_c(n)*v(n), beta=sum v(n). This is exactly the existing paired_first_jet_tail budget, including every actual prime power and the complete pole, refined Gamma and mixed terms.

**Theorem 1.9 (The actual paired column has a quantitative lower tail).**

$$\operatorname{Forall}(c, N, S, v, A) \operatorname{let}(alpha, \operatorname{sum}(n, S, \operatorname{mul}(\operatorname{complexCast}(\operatorname{arithmeticBoundarySymbol}(c, n)), \operatorname{v}(n)))) \operatorname{let}(beta, \operatorname{sum}(n, S, \operatorname{v}(n))) \operatorname{let}(q, \operatorname{add}(\operatorname{square}(\operatorname{norm}(alpha)), \operatorname{mul}(\operatorname{square}(\operatorname{smoothFloor}(c)), \operatorname{square}(\operatorname{norm}(beta))))) \operatorname{let}(U, \operatorname{div}(\operatorname{mul}(2, \operatorname{sub}(\operatorname{cosh}(\operatorname{div}(\operatorname{logLength}(c), 2)), 1)), \operatorname{div}(\operatorname{mul}(2, pi), \operatorname{logLength}(c)))) \operatorname{let}(D0, \operatorname{mul}(2, \operatorname{primeFirstMoment}(c), \operatorname{add}(2, U))) \operatorname{And}(\operatorname{AtLeastTwo}(c), \operatorname{PositiveNatural}(N), \operatorname{FiniteIntegerHead}(S), \operatorname{ComplexCoefficients}(v), \operatorname{Nonnegative}(A), \operatorname{HeadWithin}(S, A), \operatorname{LessEqual}(1, \operatorname{frequency}(c, \operatorname{add}(N, 1))), \operatorname{LessEqual}(\operatorname{mul}(2, A), \operatorname{add}(N, 1)), \operatorname{Positive}(q), \operatorname{LessEqual}(\operatorname{div}(\operatorname{mul}(2, \operatorname{square}(\operatorname{norm}(beta)), D0), q), \operatorname{add}(N, 1)), \operatorname{LessEqual}(\operatorname{div}(\operatorname{mul}(256, \operatorname{square}(\operatorname{arithmeticBoundaryBudget}(c)), \operatorname{square}(\operatorname{weightedHeadMass}(S, v))), \operatorname{mul}(3, q)), \operatorname{square}(N)))\Rightarrow\operatorname{And}(\operatorname{Summable}(\operatorname{lambda}(j, \operatorname{add}(\operatorname{square}(\operatorname{norm}(\operatorname{couplingColumn}(c, S, v, \operatorname{add}(N, j, 1)))), \operatorname{square}(\operatorname{norm}(\operatorname{couplingColumn}(c, S, v, \operatorname{neg}(\operatorname{add}(N, j, 1)))))))), \operatorname{LessEqual}(\operatorname{div}(q, \operatorname{mul}(4, \operatorname{square}(pi), \operatorname{add}(N, 1))), \operatorname{tsum}(j, \operatorname{add}(\operatorname{square}(\operatorname{norm}(\operatorname{couplingColumn}(c, S, v, \operatorname{add}(N, j, 1)))), \operatorname{square}(\operatorname{norm}(\operatorname{couplingColumn}(c, S, v, \operatorname{neg}(\operatorname{add}(N, j, 1)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualFullSymbolTail.paired_coupling_column_tail_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SOURCE_ONLY_UNCOMPILED. For every natural c>=2 and M>0, every finite S subset Z, every v:Z->C, and real A>=0 with abs(n)<=A on S, use the actual moments alpha=sum_{n in S}(arithmeticBoundarySymbol(c,n):C)*v(n) and beta=sum_{n in S}v(n). Put delta=smoothFloor(c)=(1-exp(-logLength(c)/2))/10, q=norm(alpha)^2+delta^2*norm(beta)^2, U=2*(cosh(logLength(c)/2)-1)/(2*pi/logLength(c)), and D0=2*primeFirstMoment(c)*(2+U). The displayed N denotes this same M; all mode arguments are integer casts.

The complete cutoffs are frequency(c,M+1)>=1, M+1>=2*A, q>0, M+1>=2*norm(beta)^2*D0/q, and M^2>=256*arithmeticBoundaryBudget(c)^2*weightedHeadMass(S,v)^2/(3*q). Under all these conditions, the exact sequence norm(couplingColumn(c,S,v,M+j+1))^2+norm(couplingColumn(c,S,v,-(M+j+1)))^2 is summable and q/(4*pi^2*(M+1)) is at most its single paired tsum.

The proof consumes the actual all-c Gamma finite-block floor in Jet, the full-real floor/coarse lower bound, the exact two-moment jet identity, the positive-real inverse-square lower comparison, and the actual reverse-energy inequality with the migrated remainder budget. The half-gap gives R<=32*B^2*weightedHeadMass^2/(3*pi^2*M^3); the last cutoff gives R<=q/(4*pi^2*(M+1)). No division by beta, B or weightedHeadMass is used.

This includes c=2 with alpha=0 and beta nonzero, and beta=0 when alpha is nonzero. A nonzero coefficient function need not give q>0. The q=0 case is excluded from this inverse-linear conclusion; the existing upper-tail remainder theorem remains available there. This is a bound for the actual arithmetic column, with no claim of worldwide novelty, signed Weil-form positivity, RH/Robin, or Fourier/physical operator identification. Kernel acceptance, complete source reconstruction and enrollment, Scribe emission, and required checks remain caller-owned and unperformed.

**Theorem 1.10 (The full paired actual column with the square-root budget).**

$$\operatorname{And}(\operatorname{AtLeastTwo}(c), \operatorname{Positive}(N), \operatorname{Nonnegative}(A), \operatorname{HeadWithin}(S, A), \operatorname{Less}(A, \operatorname{add}(N, 1)))\Rightarrow\operatorname{And}(\operatorname{Summable}(\operatorname{PairedColumnSequence}(c, N, S, v)), \operatorname{LessEqual}(\operatorname{PairedColumnTsum}(c, N, S, v), \operatorname{square}(\operatorname{add}(\operatorname{sqrt}(\operatorname{J}(c, N, S, v)), \operatorname{sqrt}(\operatorname{R}(c, N, A, S, v))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualFullSymbolTail.paired_coupling_column_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

SOURCE_ONLY_UNCOMPILED. Under precisely c>=2, M>0, A>=0, A<M+1, abs(n)<=A on arbitrary finite S, and arbitrary complex v, the sequence norm(couplingColumn(m))^2+norm(couplingColumn(-m))^2 for m=M+j+1 is summable and its genuine tsum is <=(sqrt(J)+sqrt(R))^2. The proof applies the pinned Real.sum_mul_le_sqrt_mul_sqrt to the finite index set range(k) times Bool, with the actual jet and column-minus-jet, obtains that same uniform partial-sum bound, and passes to the infinite nonnegative sum. No fixed factor-two energy loss is introduced. In the two-moment-annihilating application alpha=beta=0, J=0, so this same bound specializes to R without any new named corollary. All assertions, imported source candidates, AST selections and Scribe DSL remain uncompiled; kernel, axioms, compiled Reg source reconstruction and enrollment, Scribe emission, reports and required CI are pending. Actual operator Fourier identification and RH positivity remain separate. The unrelated FIB five-probability-mode model is not identified with five arbitrary Fourier coefficients. No Pro participation or diverse consensus is claimed; latest proper broker readiness is refresh_token_expired.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFullSymbolTail.fullSymbolTailBudget`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFullSymbolTail.full_symbol_square_tail`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFullSymbolTail.pairedJetBudget`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFullSymbolTail.paired_coupling_column_tail`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFullSymbolTail.paired_coupling_column_tail_lower`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFullSymbolTail.paired_first_jet_tail`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFullSymbolTail.primeFirstMoment`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFullSymbolTail.prime_first_moment_block`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFullSymbolTail.signed_mixed_partial`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFullSymbolTail.signed_mixed_tail`
- Dependency: [D5/S3/Weil/ZetaBridge/ActualColumnRemainder](ActualColumnRemainder.md)
- Dependency: [D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare](PrimeSymbolMeanSquare.md)
- Dependency: [D5/S3/Weil/ZetaBridge/PrimeSymbolResonance](PrimeSymbolResonance.md)
- Dependency: [D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingParityGram](WeilArithmeticCouplingParityGram.md)

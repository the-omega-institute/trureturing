# Actual finite head faithfulness and polynomial lower tails

## Abstract

Qualitative faithfulness and eventual polynomial lower tails for actual finite arithmetic heads.

**Theorem 1.1 (Exterior nullity determines every finite head coefficient).**

$$\operatorname{Forall}(\operatorname{Typed}(c, \operatorname{Nat}()), \operatorname{LessEqual}(2, c)\Rightarrow\operatorname{Forall}(\operatorname{Typed}(S, \operatorname{Finset}(\operatorname{Int}())), \operatorname{Forall}(\operatorname{Typed}(v, \operatorname{Function}(\operatorname{Int}(), \operatorname{Complex}())), \operatorname{Forall}(\operatorname{Typed}(M, \operatorname{Nat}()), \operatorname{Forall}(\operatorname{Typed}(m, \operatorname{Int}()), \operatorname{Less}(\operatorname{NatCastReal}(M), \operatorname{abs}(\operatorname{IntCastReal}(m)))\Rightarrow\operatorname{couplingColumn}(c, S, v, m)=0)\Rightarrow\operatorname{Forall}(\operatorname{Typed}(n, \operatorname{Int}()), \operatorname{Member}(n, S)\Rightarrow\operatorname{apply}(v, n)=0)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualFiniteHeadFaithfulness.actual_finite_head_faithful` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural c with 2 <= c, every finite set S of integers, every function v from integers to complex numbers, and every natural M, if every integer m with (M : Real) < abs((m : Real)) satisfies couplingColumn(c,S,v,m)=0, then v(n)=0 for every n in S.

The cutoff M may be zero, S may be empty or contain zero, and v has arbitrary complex values on all integers. Both positive and negative exterior modes are included by abs(m)>M. No head-radius bound, positive moment, nonempty-head, real-coefficient or weighted-null hypothesis is assumed; all radius bounds and analytic cutoffs are constructed in the proof.

The actual couplingColumn(c,S,v,m) is the finite sum over n in S of the complex cast of (arithmeticBoundarySymbol(c,n)-arithmeticBoundarySymbol(c,m))/(pi*((m : Real)-(n : Real))), multiplied by v(n). Division is totalized exactly as in the definition, including m=n. Write C_v(m)=couplingColumn(c,S,v,m).

For the symbol at an integer r, write ell=log(c), omega=2*pi*r/ell and a(j)=2*j+1/2. The full symbol is arithmeticBoundarySymbol(c,r)=-2*omega*(cosh(ell/2)-1)/(omega^2+1/4)-sum over natural j of omega*(1-exp(-a(j)*ell))/(a(j)^2+omega^2)-sum over j in range(c) of (vonMangoldt(j)/sqrt(j))*sin(omega*log(j)). The pole term, entire infinite Gamma series and finite prime sum are all retained.

With A_c(n)=arithmeticBoundarySymbol(c,n), alpha=sum over n in S of (A_c(n) : Complex)*v(n) and beta=sum over n in S of v(n), the exact coupling_column_recurrence is C_(n*v)(m)=(m : Complex)*C_v(m)-(alpha-(A_c(m) : Complex)*beta)/pi. The summand identity also covers the totalized diagonal: when m=n both symbol differences vanish. The factor 1/pi is essential.

Put delta=smoothFloor(c)=(1-exp(-logLength(c)/2))/10, which is positive for c>=2. The exterior_null_moments argument uses ActualFullSymbolTail.paired_coupling_column_tail_lower at both signs. If q=norm(alpha)^2+delta^2*norm(beta)^2 were positive, an internally chosen cutoff beyond M would give a strictly positive lower tail, whereas exterior nullity makes every term zero. Thus q=0 and alpha=beta=0; positivity of q is a contradiction case inside the proof.

The recurrence therefore propagates exterior nullity from v(n) to n*v(n), and induction propagates it to (n : Complex)^j*v(n) for every natural j. Applying the same argument at each power gives all finite node moments zero. The existing FiniteVandermondeTomography.finite_moment_readout_injective, applied to the distinct complex casts of the finite integer nodes, then forces every coefficient on S to vanish. The argument includes the empty head.

**Theorem 1.2 (The actual paired exterior energy has a head-dependent polynomial lower bound).**

$$\operatorname{Forall}(\operatorname{Typed}(c, \operatorname{Nat}()), \operatorname{LessEqual}(2, c)\Rightarrow\operatorname{Forall}(\operatorname{Typed}(S, \operatorname{Finset}(\operatorname{Int}())), \operatorname{Forall}(\operatorname{Typed}(v, \operatorname{Function}(\operatorname{Int}(), \operatorname{Complex}())), \operatorname{Exists}(\operatorname{Typed}(n, \operatorname{Int}()), \operatorname{And}(\operatorname{Member}(n, S), \operatorname{NotEqual}(\operatorname{apply}(v, n), 0)))\Rightarrow\operatorname{Exists}(\operatorname{Typed}(k, \operatorname{Nat}()), \operatorname{And}(\operatorname{Less}(k, \operatorname{Card}(S)), \operatorname{Exists}(\operatorname{Typed}(C, \operatorname{Real}()), \operatorname{And}(\operatorname{Less}(0, C), \operatorname{Exists}(\operatorname{Typed}(N0, \operatorname{Nat}()), \operatorname{Forall}(\operatorname{Typed}(N, \operatorname{Nat}()), \operatorname{LessEqual}(N0, N)\Rightarrow\operatorname{And}(\operatorname{Summable}(\operatorname{Lambda}(\operatorname{Typed}(j, \operatorname{Nat}()), \operatorname{Add}(\operatorname{Pow}(\operatorname{norm}(\operatorname{couplingColumn}(c, S, v, \operatorname{NatCastInt}(\operatorname{Add}(\operatorname{Add}(N, j), 1)))), 2), \operatorname{Pow}(\operatorname{norm}(\operatorname{couplingColumn}(c, S, v, \operatorname{Neg}(\operatorname{NatCastInt}(\operatorname{Add}(\operatorname{Add}(N, j), 1))))), 2)))), \operatorname{LessEqual}(\operatorname{Div}(C, \operatorname{Pow}(\operatorname{Add}(\operatorname{NatCastReal}(N), 1), \operatorname{Add}(\operatorname{Mul}(2, k), 1))), \operatorname{Tsum}(\operatorname{Typed}(j, \operatorname{Nat}()), \operatorname{Add}(\operatorname{Pow}(\operatorname{norm}(\operatorname{couplingColumn}(c, S, v, \operatorname{NatCastInt}(\operatorname{Add}(\operatorname{Add}(N, j), 1)))), 2), \operatorname{Pow}(\operatorname{norm}(\operatorname{couplingColumn}(c, S, v, \operatorname{Neg}(\operatorname{NatCastInt}(\operatorname{Add}(\operatorname{Add}(N, j), 1))))), 2))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ActualFiniteHeadFaithfulness.actual_finite_head_polynomial_tail_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural c with 2 <= c, every finite set S of integers and every complex coefficient function v on the integers, if there is n in S with v(n) != 0, then there exist a natural k < card(S), a real C > 0 and a natural N0 such that for every natural N with N0 <= N, the sequence j |-> norm(couplingColumn(c,S,v,Int.ofNat(N+j+1)))^2 + norm(couplingColumn(c,S,v,-Int.ofNat(N+j+1)))^2 is Summable and its actual tsum is at least C / ((N : Real)+1)^(2*k+1). No positive original moment, head radius or analytic cutoff is a premise. The exponent, positive constant and cutoff depend on the actual head; this is not a uniform inverse bound.

Write w_j(n)=(n : Complex)^j*v(n), alpha_j=sum over n in S of (A_c(n) : Complex)*w_j(n), beta_j=sum over n in S of w_j(n), and q_j=norm(alpha_j)^2+delta^2*norm(beta_j)^2. Since delta>0, q_j<=0 forces alpha_j=beta_j=0. If every q_j for j<card(S) failed to be positive, the first card(S) beta moments and finite_moment_readout_injective would force every coefficient on S to vanish. Hence the least positive moment energy q_k has k<card(S), and both moments vanish at every smaller index.

The exact recurrence C_(n*w)(m)=(m : Complex)*C_w(m)-(alpha(w)-(A_c(m) : Complex)*beta(w))/pi cancels its final term at every smaller index. Consequently C_(w_k)(m)=(m : Complex)^k*C_v(m) for every integer m, including the totalized diagonal and both signs. If e_w(m)=norm(C_w(Int.ofNat(m)))^2+norm(C_w(-Int.ofNat(m)))^2 for natural m, norm multiplicativity and norm of negation give e_(w_k)(m)=(m : Real)^(2*k)*e_v(m). No parity or vanishing condition is imposed on v. Set E_w(N)=tsum over natural j of e_w(N+j+1).

Construct the radius R=sum over n in S of abs((n : Real)), which bounds each head index. Put B=arithmeticBoundaryBudget(c) and H(w)=sum over n in S of norm(w(n)). The actual arithmetic_boundary_symbol_bound gives abs(A_c(n)),abs(A_c(m))<=B. For abs(m)>=2*R and abs(m)>0, abs(m-n)>=abs(m)/2. Each divided-difference coefficient has norm at most 4*B/(pi*abs(m)), so norm(C_w(m))<=4*B*H(w)/(pi*abs(m)). Squaring both exterior signs bounds e_w(m) by 32*B^2*H(w)^2/(pi^2*m^2). The existing inverse_square_partial_le bounds the finite partial sums, and Real.tsum_le_of_sum_range_le yields E_w(N)<=U/N with U=32*B^2*H(w)^2/pi^2 whenever N>=2*R and N>0. Summability comes from ActualFullSymbolTail.paired_coupling_column_tail at the internally verified separation.

For w=w_k and q=q_k>0, choose a natural L>=1 with 8*pi^2*U/q<=L. Choose N0 beyond 1, 2*R, logLength(c)/(2*pi), 2*norm(beta_k)^2*D0/q, and 256*B^2*weightedHeadMass(S,w)^2/(3*q), where P=2*(cosh(logLength(c)/2)-1)/(2*pi/logLength(c)) and D0=2*primeFirstMoment(c)*(2+P). For N>=N0, N<=N^2 verifies the weighted-remainder cutoff, and the frequency, gap and signed-mixed cutoffs also hold. The actual paired_coupling_column_tail_lower gives E_w(N)>=q/(4*pi^2*(N+1)). These choices construct the required cutoffs from the head.

Set T=L*(N+1). The actual upper tail satisfies E_w(T)<=U/T<=q/(8*pi^2*(N+1)). Summable.sum_add_tsum_nat_add with length T-N, using N<=T to identify the shifted indices, gives E_w(N)-E_w(T)=sum over j<T-N of e_w(N+j+1). This genuine finite annulus therefore has energy at least q/(8*pi^2*(N+1)).

On the annulus, N+j+1<=T, so the exact both-sign power identity gives e_w(N+j+1)<=(T : Real)^(2*k)*e_v(N+j+1). Summable.sum_le_tsum bounds the unweighted finite sum by E_v(N). Dividing the resulting inequality by the positive (T : Real)^(2*k) gives C=q/(8*pi^2*(L : Real)^(2*k))>0 and E_v(N)>=C/(N+1)^(2*k+1). The comparison uses the bounded modes of a finite annulus, with summability established for the actual tails.

The even three-point stencil at {n,-n,0}, for any nonzero integer n, has coefficients (1,1,-2) and is a nonzero finite head. Its original moments are beta_0=1+1-2=0 and alpha_0=A_c(n)+A_c(-n)-2*A_c(0)=0, since the full symbol is odd and A_c(0)=0. Thus q_0=0. This illustrates why positivity of q_0 is not assumed; the least positive higher moment supplies the argument above.

The mathematical provenance is the standard finite-moment/Vandermonde argument and tail subtraction on a finite annulus, applied to the actual full arithmetic symbol. No novelty, physical-operator identification, signed Weil positivity, Robin5040 or RH conclusion is claimed.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFiniteHeadFaithfulness.actual_finite_head_faithful`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ActualFiniteHeadFaithfulness.actual_finite_head_polynomial_tail_lower`
- Dependency: [D5/S3/Analytic/GoldenTomography/FiniteVandermondeTomography](../../Analytic/GoldenTomography/FiniteVandermondeTomography.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ActualFullSymbolTail](ActualFullSymbolTail.md)

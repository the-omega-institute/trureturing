using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ActualFiniteHeadFaithfulnessDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaBridge/ActualFiniteHeadFaithfulness.";

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new System.Collections.Generic.List<Formula>
            { Operatorname, Grp(F.Id(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }

    public DocumentDefinition Create()
    {
        Formula c = F.Id("c"), S = F.Id("S"), v = F.Id("v");
        Formula M = F.Id("M"), m = F.Id("m"), n = F.Id("n");
        Formula exteriorNullity = Call("Forall", Call("Typed", m, Call("Int")),
            Seq(Call("Less", Call("NatCastReal", M), Call("abs", Call("IntCastReal", m))),
                Rightarrow, Seq(Call("couplingColumn", c, S, v, m), Eq, D(0))));
        Formula coefficientNullity = Call("Forall", Call("Typed", n, Call("Int")),
            Seq(Call("Member", n, S), Rightarrow, Seq(Call("apply", v, n), Eq, D(0))));
        Formula qualitativeAuthorStatement = Call("Forall", Call("Typed", c, Call("Nat")),
            Seq(Call("LessEqual", D(2), c), Rightarrow,
                Call("Forall", Call("Typed", S, Call("Finset", Call("Int"))),
                    Call("Forall", Call("Typed", v, Call("Function", Call("Int"), Call("Complex"))),
                        Call("Forall", Call("Typed", M, Call("Nat")),
                            Seq(exteriorNullity, Rightarrow, coefficientNullity))))));

        Formula k = F.Id("k"), C = F.Id("C");
        Formula N0 = F.Id("N0"), N = F.Id("N"), j = F.Id("j");
        Formula mode = Call("NatCastInt", Call("Add", Call("Add", N, j), D(1)));
        Formula positiveColumn = Call("couplingColumn", c, S, v, mode);
        Formula negativeColumn = Call("couplingColumn", c, S, v, Call("Neg", mode));
        Formula pairedEnergy = Call("Add", Call("Pow", Call("norm", positiveColumn), D(2)),
            Call("Pow", Call("norm", negativeColumn), D(2)));
        Formula summability = Call("Summable",
            Call("Lambda", Call("Typed", j, Call("Nat")), pairedEnergy));
        Formula exponent = Call("Add", Call("Mul", D(2), k), D(1));
        Formula lowerBound = Call("LessEqual",
            Call("Div", C, Call("Pow", Call("Add", Call("NatCastReal", N), D(1)), exponent)),
            Call("Tsum", Call("Typed", j, Call("Nat")), pairedEnergy));
        Formula nonzeroHead = Call("Exists", Call("Typed", n, Call("Int")),
            Call("And", Call("Member", n, S), Call("NotEqual", Call("apply", v, n), D(0))));
        Formula eventualBound = Call("Forall", Call("Typed", N, Call("Nat")),
            Seq(Call("LessEqual", N0, N), Rightarrow, Call("And", summability, lowerBound)));
        Formula quantitativeConclusion = Call("Exists", Call("Typed", k, Call("Nat")),
            Call("And", Call("Less", k, Call("Card", S)),
                Call("Exists", Call("Typed", C, Call("Real")),
                    Call("And", Call("Less", D(0), C),
                        Call("Exists", Call("Typed", N0, Call("Nat")), eventualBound)))));
        Formula quantitativeAuthorStatement = Call("Forall", Call("Typed", c, Call("Nat")),
            Seq(Call("LessEqual", D(2), c), Rightarrow,
                Call("Forall", Call("Typed", S, Call("Finset", Call("Int"))),
                    Call("Forall", Call("Typed", v, Call("Function", Call("Int"), Call("Complex"))),
                        Seq(nonzeroHead, Rightarrow, quantitativeConclusion)))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Qualitative faithfulness and eventual polynomial lower tails for actual finite arithmetic heads.",
            H("Actual finite head faithfulness and polynomial lower tails"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("actual-finite-head-faithful"),
                    DeclarationHandle.Create(Owner + "actual_finite_head_faithful"),
                    H("Exterior nullity determines every finite head coefficient"),
                    StatementSource.FromAuthor(Disp(qualitativeAuthorStatement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For every natural c with 2 <= c, every finite set S of integers, every function v from integers to complex numbers, and every natural M, if every integer m with (M : Real) < abs((m : Real)) satisfies couplingColumn(c,S,v,m)=0, then v(n)=0 for every n in S.")),
                        Paragraph(Text("The cutoff M may be zero, S may be empty or contain zero, and v has arbitrary complex values on all integers. Both positive and negative exterior modes are included by abs(m)>M. No head-radius bound, positive moment, nonempty-head, real-coefficient or weighted-null hypothesis is assumed; all radius bounds and analytic cutoffs are constructed in the proof.")),
                        Paragraph(Text("The actual couplingColumn(c,S,v,m) is the finite sum over n in S of the complex cast of (arithmeticBoundarySymbol(c,n)-arithmeticBoundarySymbol(c,m))/(pi*((m : Real)-(n : Real))), multiplied by v(n). Division is totalized exactly as in the definition, including m=n. Write C_v(m)=couplingColumn(c,S,v,m).")),
                        Paragraph(Text("For the symbol at an integer r, write ell=log(c), omega=2*pi*r/ell and a(j)=2*j+1/2. The full symbol is arithmeticBoundarySymbol(c,r)=-2*omega*(cosh(ell/2)-1)/(omega^2+1/4)-sum over natural j of omega*(1-exp(-a(j)*ell))/(a(j)^2+omega^2)-sum over j in range(c) of (vonMangoldt(j)/sqrt(j))*sin(omega*log(j)). The pole term, entire infinite Gamma series and finite prime sum are all retained.")),
                        Paragraph(Text("With A_c(n)=arithmeticBoundarySymbol(c,n), alpha=sum over n in S of (A_c(n) : Complex)*v(n) and beta=sum over n in S of v(n), the exact coupling_column_recurrence is C_(n*v)(m)=(m : Complex)*C_v(m)-(alpha-(A_c(m) : Complex)*beta)/pi. The summand identity also covers the totalized diagonal: when m=n both symbol differences vanish. The factor 1/pi is essential.")),
                        Paragraph(Text("Put delta=smoothFloor(c)=(1-exp(-logLength(c)/2))/10, which is positive for c>=2. The exterior_null_moments argument uses ActualFullSymbolTail.paired_coupling_column_tail_lower at both signs. If q=norm(alpha)^2+delta^2*norm(beta)^2 were positive, an internally chosen cutoff beyond M would give a strictly positive lower tail, whereas exterior nullity makes every term zero. Thus q=0 and alpha=beta=0; positivity of q is a contradiction case inside the proof.")),
                        Paragraph(Text("The recurrence therefore propagates exterior nullity from v(n) to n*v(n), and induction propagates it to (n : Complex)^j*v(n) for every natural j. Applying the same argument at each power gives all finite node moments zero. The existing FiniteVandermondeTomography.finite_moment_readout_injective, applied to the distinct complex casts of the finite integer nodes, then forces every coefficient on S to vanish. The argument includes the empty head."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("actual-finite-head-polynomial-tail-lower"),
                    DeclarationHandle.Create(Owner + "actual_finite_head_polynomial_tail_lower"),
                    H("The actual paired exterior energy has a head-dependent polynomial lower bound"),
                    StatementSource.FromAuthor(Disp(quantitativeAuthorStatement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For every natural c with 2 <= c, every finite set S of integers and every complex coefficient function v on the integers, if there is n in S with v(n) != 0, then there exist a natural k < card(S), a real C > 0 and a natural N0 such that for every natural N with N0 <= N, the sequence j |-> norm(couplingColumn(c,S,v,Int.ofNat(N+j+1)))^2 + norm(couplingColumn(c,S,v,-Int.ofNat(N+j+1)))^2 is Summable and its actual tsum is at least C / ((N : Real)+1)^(2*k+1). No positive original moment, head radius or analytic cutoff is a premise. The exponent, positive constant and cutoff depend on the actual head; this is not a uniform inverse bound.")),
                        Paragraph(Text("Write w_j(n)=(n : Complex)^j*v(n), alpha_j=sum over n in S of (A_c(n) : Complex)*w_j(n), beta_j=sum over n in S of w_j(n), and q_j=norm(alpha_j)^2+delta^2*norm(beta_j)^2. Since delta>0, q_j<=0 forces alpha_j=beta_j=0. If every q_j for j<card(S) failed to be positive, the first card(S) beta moments and finite_moment_readout_injective would force every coefficient on S to vanish. Hence the least positive moment energy q_k has k<card(S), and both moments vanish at every smaller index.")),
                        Paragraph(Text("The exact recurrence C_(n*w)(m)=(m : Complex)*C_w(m)-(alpha(w)-(A_c(m) : Complex)*beta(w))/pi cancels its final term at every smaller index. Consequently C_(w_k)(m)=(m : Complex)^k*C_v(m) for every integer m, including the totalized diagonal and both signs. If e_w(m)=norm(C_w(Int.ofNat(m)))^2+norm(C_w(-Int.ofNat(m)))^2 for natural m, norm multiplicativity and norm of negation give e_(w_k)(m)=(m : Real)^(2*k)*e_v(m). No parity or vanishing condition is imposed on v. Set E_w(N)=tsum over natural j of e_w(N+j+1).")),
                        Paragraph(Text("Construct the radius R=sum over n in S of abs((n : Real)), which bounds each head index. Put B=arithmeticBoundaryBudget(c) and H(w)=sum over n in S of norm(w(n)). The actual arithmetic_boundary_symbol_bound gives abs(A_c(n)),abs(A_c(m))<=B. For abs(m)>=2*R and abs(m)>0, abs(m-n)>=abs(m)/2. Each divided-difference coefficient has norm at most 4*B/(pi*abs(m)), so norm(C_w(m))<=4*B*H(w)/(pi*abs(m)). Squaring both exterior signs bounds e_w(m) by 32*B^2*H(w)^2/(pi^2*m^2). The existing inverse_square_partial_le bounds the finite partial sums, and Real.tsum_le_of_sum_range_le yields E_w(N)<=U/N with U=32*B^2*H(w)^2/pi^2 whenever N>=2*R and N>0. Summability comes from ActualFullSymbolTail.paired_coupling_column_tail at the internally verified separation.")),
                        Paragraph(Text("For w=w_k and q=q_k>0, choose a natural L>=1 with 8*pi^2*U/q<=L. Choose N0 beyond 1, 2*R, logLength(c)/(2*pi), 2*norm(beta_k)^2*D0/q, and 256*B^2*weightedHeadMass(S,w)^2/(3*q), where P=2*(cosh(logLength(c)/2)-1)/(2*pi/logLength(c)) and D0=2*primeFirstMoment(c)*(2+P). For N>=N0, N<=N^2 verifies the weighted-remainder cutoff, and the frequency, gap and signed-mixed cutoffs also hold. The actual paired_coupling_column_tail_lower gives E_w(N)>=q/(4*pi^2*(N+1)). These choices construct the required cutoffs from the head.")),
                        Paragraph(Text("Set T=L*(N+1). The actual upper tail satisfies E_w(T)<=U/T<=q/(8*pi^2*(N+1)). Summable.sum_add_tsum_nat_add with length T-N, using N<=T to identify the shifted indices, gives E_w(N)-E_w(T)=sum over j<T-N of e_w(N+j+1). This genuine finite annulus therefore has energy at least q/(8*pi^2*(N+1)).")),
                        Paragraph(Text("On the annulus, N+j+1<=T, so the exact both-sign power identity gives e_w(N+j+1)<=(T : Real)^(2*k)*e_v(N+j+1). Summable.sum_le_tsum bounds the unweighted finite sum by E_v(N). Dividing the resulting inequality by the positive (T : Real)^(2*k) gives C=q/(8*pi^2*(L : Real)^(2*k))>0 and E_v(N)>=C/(N+1)^(2*k+1). The comparison uses the bounded modes of a finite annulus, with summability established for the actual tails.")),
                        Paragraph(Text("The even three-point stencil at {n,-n,0}, for any nonzero integer n, has coefficients (1,1,-2) and is a nonzero finite head. Its original moments are beta_0=1+1-2=0 and alpha_0=A_c(n)+A_c(-n)-2*A_c(0)=0, since the full symbol is odd and A_c(0)=0. Thus q_0=0. This illustrates why positivity of q_0 is not assumed; the least positive higher moment supplies the argument above.")),
                        Paragraph(Text("The mathematical provenance is the standard finite-moment/Vandermonde argument and tail subtraction on a finite annulus, applied to the actual full arithmetic symbol. No novelty, physical-operator identification, signed Weil positivity, Robin5040 or RH conclusion is claimed."))),
                    DescribeRole.Theorem))));
    }
}

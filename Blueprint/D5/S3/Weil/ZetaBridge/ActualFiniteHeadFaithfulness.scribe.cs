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
        Formula authorStatement = Call("Forall", Call("Typed", c, Call("Nat")),
            Seq(Call("LessEqual", D(2), c), Rightarrow,
                Call("Forall", Call("Typed", S, Call("Finset", Call("Int"))),
                    Call("Forall", Call("Typed", v, Call("Function", Call("Int"), Call("Complex"))),
                        Call("Forall", Call("Typed", M, Call("Nat")),
                            Seq(exteriorNullity, Rightarrow, coefficientNullity))))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "SOURCE_ONLY_UNCOMPILED: author statement for qualitative actual finite-head faithfulness; all acceptance checks remain unperformed.",
            H("Actual Finite Head Faithfulness"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("actual-finite-head-faithful"),
                    DeclarationHandle.Create(Owner + "actual_finite_head_faithful"),
                    H("Exterior nullity determines every finite head coefficient"),
                    StatementSource.FromAuthor(Disp(authorStatement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("SOURCE_ONLY_UNCOMPILED. For every natural c with 2 <= c, every finite set S of integers, every function v from integers to complex numbers, and every natural M, if for every integer m the inequality (M : Real) < abs((m : Real)) implies couplingColumn(c,S,v,m)=0, then for every integer n, membership n in S implies v(n)=0. This is the full quantified author statement of the exact owner actual_finite_head_faithful; c is implicit in Lean, and hc and hnull are the displayed hypothesis proofs.")),
                        Paragraph(Text("The cutoff M may be zero, S may be empty or contain zero, and v has arbitrary complex values on all integers. Both positive and negative exterior modes are required by abs(m)>M. No head-radius bound, positive moment, q>0, nonempty-head, real-coefficient or weighted-null hypothesis is added. Radius bounds and all analytic cutoffs used in the source proof are constructed internally.")),
                        Paragraph(Text("The actual couplingColumn(c,S,v,m) is the finite sum over n in S of the complex cast of (arithmeticBoundarySymbol(c,n)-arithmeticBoundarySymbol(c,m))/(pi*((m : Real)-(n : Real))), multiplied by v(n). Division is totalized exactly as in the source, including m=n. This retains the actual arithmetic symbol and is not a column made from a freely chosen substitute symbol.")),
                        Paragraph(Text("For the symbol at an integer k, write L=log(c), w=2*pi*k/L and a(j)=2*j+1/2. The pinned definition is arithmeticBoundarySymbol(c,k)=-2*w*(cosh(L/2)-1)/(w^2+1/4)-sum over natural j of w*(1-exp(-a(j)*L))/(a(j)^2+w^2)-sum over j in range(c) of (vonMangoldt(j)/sqrt(j))*sin(w*log(j)). These are the pole, infinite Gamma and finite prime parts, all retained; the lower-chain source candidate supplies the Gamma convergence argument.")),
                        Paragraph(Text("The pinned owner's private coupling_column_recurrence states C(n*v)(m)=m*C(v)(m)-(alpha-symbol(m)*beta)/pi, where alpha=sum over n in S of symbol(n)*v(n), beta=sum over n in S of v(n), symbol=arithmeticBoundarySymbol(c) and C(v)=couplingColumn(c,S,v). The essential factor 1/pi is retained. The totalized diagonal is covered by the summand recurrence.")),
                        Paragraph(Text("The private exterior_null_moments argument consumes ActualFullSymbolTail.paired_coupling_column_tail_lower for the actual columns at both signs. If q=norm(alpha)^2+smoothFloor(c)^2*norm(beta)^2 were positive, an internally chosen cutoff beyond M would give a positive lower bound for a tail that exterior nullity makes zero. Hence q=0, and positivity of smoothFloor(c) for c>=2 forces both alpha=0 and beta=0. Positivity of q is a contradiction case inside the proof, not a theorem premise.")),
                        Paragraph(Text("The recurrence propagates exterior nullity from v(n) to n*v(n); induction propagates it to every node power n^k*v(n). Applying the same moment argument at each power gives all finite node moments zero. The owner then consumes the existing FiniteVandermondeTomography.finite_moment_readout_injective with injective complex casts of the finite integer nodes, so every coefficient on S vanishes, including the empty-head case.")),
                        Paragraph(Text("This is qualitative finite-head faithfulness for actual arithmetic divided-difference columns. It does not establish signed Weil positivity, Robin5040, RH, a quantitative inverse bound, or identification with a physical or canonical Weil operator. The owner and the actual lower-chain dependencies are saved UNCOMPILED source candidates.")),
                        Paragraph(Text("Only source bytes, textual structure and balanced delimiters are checked here. Lean elaboration and real kernel checking, axiom and proof-trust inspection, Reg bridge and whole-family obligations, support enrollment and universes, raw Expr source-selector reconstruction and exact occurrence binding, Scribe compilation and AST/schema/owner checks, rendering and provenance assessment, and every required CI or official acceptance check remain unperformed. Every sourceSelection Expr path in the companion Reg source remains unverified pending actual compilation and inspection."))),
                    DescribeRole.Theorem))));
    }
}

// Isolated quantitative continuation. The original document above is unchanged.
internal sealed class ActualFiniteHeadPolynomialTailLowerDocument : IScribeDocumentDefinition
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
        Formula n = F.Id("n"), k = F.Id("k"), C = F.Id("C");
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
        Formula authorStatement = Call("Forall", Call("Typed", c, Call("Nat")),
            Seq(Call("LessEqual", D(2), c), Rightarrow,
                Call("Forall", Call("Typed", S, Call("Finset", Call("Int"))),
                    Call("Forall", Call("Typed", v, Call("Function", Call("Int"), Call("Complex"))),
                        Seq(nonzeroHead, Rightarrow, quantitativeConclusion)))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "SOURCE_ONLY_UNVALIDATED: quantitative source proof and registration attempt; native checks pending.",
            H("An eventual polynomial lower tail for every nonzero finite head"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("actual-finite-head-polynomial-tail-lower"),
                    DeclarationHandle.Create(Owner + "actual_finite_head_polynomial_tail_lower"),
                    H("The actual paired exterior energy has a head-dependent polynomial lower bound"),
                    StatementSource.FromAuthor(Disp(authorStatement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("For every natural c with 2 <= c, every finite set S of integers and every complex coefficient function v on the integers, if there is n in S with v(n) != 0, then there exist a natural k < card(S), a real C > 0 and a natural N0 such that for every natural N with N0 <= N, the sequence j |-> norm(couplingColumn(c,S,v,Int.ofNat(N+j+1)))^2 + norm(couplingColumn(c,S,v,-Int.ofNat(N+j+1)))^2 is Summable and its actual tsum is at least C / ((N : Real)+1)^(2*k+1). These are exactly the hypotheses, quantifiers, two exterior signs, normalization and conclusion of actual_finite_head_polynomial_tail_lower. Neither a positive original moment nor a head radius nor an analytic cutoff is a premise. The constants depend on the actual head and are not uniform in v.")),
                        Paragraph(Text("The pinned original qualitative D5 and Reg are recorded in inputs/actual-qualitative-acceptance.json as compiled with only Classical.choice, Quot.sound and propext, and the original registration as declared_validated. The preserved original comments and saved quantitative plan predate that record. Their native-premise waiting condition is satisfied. This continuation is source only: it has not been compiled, axiom-audited, source-bound or accepted by Scribe or CI. Pro was unavailable with refresh_token_expired; there is no Pro approval or independent consensus.")),
                        Paragraph(Text("Write A(n)=arithmeticBoundarySymbol(c,n), w_j(n)=(n : Complex)^j*v(n), alpha_j=sum over n in S of (A(n) : Complex)*w_j(n), beta_j=sum over n in S of w_j(n), and q_j=norm(alpha_j)^2+smoothFloor(c)^2*norm(beta_j)^2. The actual full pole, Gamma and prime symbol remains in couplingColumn. Positivity of smoothFloor(c) for c>=2 makes q_j<=0 force alpha_j=beta_j=0. If every q_j for j<card(S) failed to be positive, the existing finite_moment_readout_injective on distinct complex casts of S would force every coefficient on S to vanish. Thus the least positive q_k has k<card(S), and both moments vanish at every smaller index.")),
                        Paragraph(Text("The original compiled private coupling_column_recurrence is reused: C_(n*w)(m)=m*C_w(m)-(alpha(w)-A(m)*beta(w))/pi. Lower moment vanishing cancels precisely that term at every induction step. It yields C_(w_k)(m)=(m : Complex)^k*C_v(m) for every integer m, including the totalized diagonal and both signs. Norm multiplicativity, norm of natural casts, norm of negation and power multiplication give pairedEnergy(w_k,m)=(m : Real)^(2*k)*pairedEnergy(v,m) for natural m. No parity or vanishing is assumed of v.")),
                        Paragraph(Text("Construct A=sum over n in S of abs((n : Real)); it bounds each head index. Put B=arithmeticBoundaryBudget(c) and H(w)=sum over n in S of norm(w(n)). The actual arithmetic_boundary_symbol_bound gives abs(A(n)),abs(A(m))<=B. For abs(m)>=2*A and abs(m)>0, the triangle inequality gives abs(m-n)>=abs(m)/2. Hence each divided-difference coefficient has norm at most 4*B/(pi*abs(m)), and the finite sum gives norm(C_w(m))<=4*B*H(w)/(pi*abs(m)). Squaring both signs gives 32*B^2*H(w)^2/(pi^2*m^2). The existing inverse_square_partial_le bounds all finite partial sums; Real.tsum_le_of_sum_range_le then proves E_w(N)<=U/N with U=32*B^2*H(w)^2/pi^2 for N>=2*A and N>0. Summability is supplied by the actual paired_coupling_column_tail at the internally verified separation.")),
                        Paragraph(Text("For w=w_k and q=q_k, choose one natural L>=1 with 8*pi^2*U/q<=L. The source chooses N0 beyond 1, 2*A, logLength(c)/(2*pi), the actual signed-mixed cutoff 2*norm(beta_k)^2*D0/q, and the weighted-remainder cutoff 256*B^2*weightedHeadMass(S,w)^2/(3*q). Here P=2*(cosh(logLength(c)/2)-1)/(2*pi/logLength(c)) and D0=2*primeFirstMoment(c)*(2+P), exactly as in the owned lower theorem. For N>=N0, N<=N^2 and the frequency, gap, mixed and remainder hypotheses are verified. The actual paired_coupling_column_tail_lower gives E_w(N)>=q/(4*pi^2*(N+1)).")),
                        Paragraph(Text("Set T=L*(N+1). The actual upper tail at T is at most U/T<=q/(8*pi^2*(N+1)). Summable.sum_add_tsum_nat_add with length T-N splits E_w(N) into the finite sum over j<T-N at modes N+j+1 and the actual tail E_w(T); the source proves the natural index equality using N<=T. Consequently that finite annulus has energy at least q/(8*pi^2*(N+1)). On it N+j+1<=T, so nonnegative-power monotonicity and the exact both-sign identity bound its weighted energy by T^(2*k) times the corresponding unweighted finite sum. Summable.sum_le_tsum bounds that finite sum by E_v(N). Division by the positive T^(2*k) gives C=q/(8*pi^2*L^(2*k))>0 and E_v(N)>=C/(N+1)^(2*k+1). The proof never divides an infinite weighted tail by a uniform exterior-mode bound.")),
                        Paragraph(Text("The companion registration attempt retains the full theorem telescope. Its actual readout is the original norm function Complex -> Real, selected at the first positive-branch norm under Summable, before its separate square. Replacing precisely that occurrence by constant one leaves the other three norm occurrences unchanged. For c=2, S={0}, v=1, the full existential rejected Law would give Summable of a sequence with every term >=1 at its own N0; finite sums and Archimedean choice contradict this. The typed family supplies bridge, variation, sensitivity and dependence using the existing enrolled DependentFamily.realize template. The proposed raw Expr path, empty coordinate packing, norm instance, fresh complex state, universes, descriptor binding and registration are unvalidated until native inspection.")),
                        Paragraph(Text("The existing zeroTraceColumn stencil at {n,-n,0} with coefficients (1,1,-2) motivates removal of the q_0>0 restriction: both original moments vanish. It is not a new delivered corollary. No N^-3 or N^-5 stencil refinement is claimed compiled. This argument has standard moment/Vandermonde/tail-annulus provenance, with no novelty claim, no physical-operator identification and no signed Weil positivity, Robin5040 or RH conclusion. Products remain isolated pending review and any later pinned rebase against concurrent Scribe changes.")),
                        Paragraph(Text("All source proof bodies are supplied without sorry, admit, new axioms or new options. Only static source checks were performed for this continuation. Lean elaboration, kernel and axiom closure, exact source occurrence binding, registration/template and Scribe/Describe/schema/owner checks, rendering, required CI and integration remain caller-owned and pending."))),
                    DescribeRole.Theorem))));
    }
}

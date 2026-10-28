using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class ExponentialTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A geometric estimate for the analytic exponential remainder in a complete normed real algebra.",
        H("Exponential remainder"),
        Blocks(Describe.Lean(DescribeId.Create("auric-omega-exponential-remainder"),
            DeclarationHandle.Create("D5/S3/Quantum/AURICOmega/ExponentialTail.exp_remainder_le"),
            H("A bound from successive factorial ratios"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Write exponentialRemainder(x,n)=exp(x)-sum from k=0 to n-1 of x^k/k!. Let B be a complete normed real algebra with a submultiplicative norm and norm of the identity equal to one. For a nonnegative r with norm(x) at most r, and r<n+1, the omitted terms of the exponential series have norms bounded by r^n/n! times (r/(n+1))^k. Summing this geometric majorant gives the displayed bound.")),
                Paragraph(Text("Mathlib supplies convergence of the exponential power series, the comparison theorem for sums in normed groups, and the sum of the geometric series. The factorial coefficient estimate joins these results without commuting products. For matrices, the induced maximum row-sum norm is submultiplicative and fits these assumptions; the entrywise maximum norm does not supply that multiplication estimate.")),
                Paragraph(Text("At r=2 and n=13 the ratio is 1/7, so the bound is (7/6) times 2^13/13!. The estimate concerns the actual exponential, rather than only a finite polynomial."))),
            DescribeRole.Theorem),
            FiveModeApplication())));

    private static Formula Call(string n, params Formula[] x) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. x]);
    private static Formula Num(int n) => F.D((byte)n);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) =>
        new Formula.Relation(x, op, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Statement()
    {
        Formula b = F.Id("B"), x = F.Id("x"), r = F.Id("r"), n = F.Id("n");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula oneMore = new Formula.Binary(n, FormulaBinaryOperator.Add, Num(1));
        Formula assumptions = And(Rel(Num(0), FormulaRelationOperator.LessThanOrEqual, r),
            And(Rel(Call("norm", x), FormulaRelationOperator.LessThanOrEqual, r),
                Rel(r, FormulaRelationOperator.LessThan, oneMore)));
        Formula conclusion = Rel(Call("norm", Call("exponentialRemainder", x, n)),
            FormulaRelationOperator.LessThanOrEqual,
            Call("divide", Call("divide", Call("power", r, n), Call("factorial", n)),
                Call("subtract", Num(1), Call("divide", r, oneMore))));
        Formula body = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("x"), b),
             new(FormulaIdentifier.Create("r"), reals),
             new(FormulaIdentifier.Create("n"), naturals)],
            new Formula.Logic(assumptions, FormulaLogicOperator.Implies, conclusion));
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("B"), Call("Type"),
            Seq(OpenBracket, Call("NormedRing", b), CloseBracket, Sp,
                OpenBracket, Call("NormedAlgebra", reals, b), CloseBracket, Sp,
                OpenBracket, Call("CompleteSpace", b), CloseBracket, Sp,
                OpenBracket, Call("NormOneClass", b), CloseBracket, Sp, body)));
    }

    private static DocumentBlock FiveModeApplication() => new DocumentBlock.Section(
        H("The actual five-mode walk at two thirds"),
        Blocks(
                Paragraph(Text("The mode order is (N,2,3,5,25), with N indexed by 0. The real generator is A=[[0,1,1,1,0],[-1,0,0,0,-1],[-1,0,0,0,0],[-1,0,0,0,-1],[0,1,0,1,0]]. Put X=(2/3)A, O=exp(X), and S=sum from k=0 to 12 of X^k/k!. The transpose relation A^T=-A and Mathlib's matrix exponential product theorem give both orthogonality identities.")),
                Paragraph(Text("The matrix norm throughout the remainder estimate is the induced maximum row-sum norm. Its bound for X is 2. The general exponential remainder theorem gives norm(O-S) at most (7/6) times 2^13/13!, equal to 4/2606175. The successive scalar majorant ratios are at most 1/7. This is smaller than 64/6081075.")),
                Paragraph(Text("The first row of S is exactly [107738440637/248594813775,490347766/1104865839,4899328858/9207215325,490347766/1104865839,-91371050044/248594813775]. Its absolute entries all exceed 367/1000. Subtracting the proved analytic remainder gives absolute entries of the actual O strictly greater than 9/25. Their squares exceed 1/8 and sum to one. The notation squareSum(v) denotes the sum of the five squared coordinates, and minimumSquaredCoordinate(v) denotes their finite minimum.")),
                Paragraph(Text("The coordinates of v=O^T e_N are the entries of the first row of the actual O, so v is a unit vector with full support. Since Fin 5 is nonempty and finite, its minimum squared coordinate exceeds 1/8. The real coordinate calculation is used within the full complex Hilbert space; it imposes no restriction to real input density matrices. The diagonal frame D=diag(1,i,i,i,1) is a passive change of coordinates. The wait 2/3 is a nonnegative mathematical parameter and supplies no physical calibration or additional operation.")),
                Paragraph(Text("Connected-probe rigidity is the standard result of Mayer and Knill, Quantum Process Fidelity Bounds from Sets of Input States, arXiv:1805.04491v1, Theorem 1. Measurement-relative compression uses the common encoder and decoder model of Bluhm, Rauber and Wolf, arXiv:1708.04898v4. Koashi and Imoto, quant-ph/0101144, provide broader no-disturbance structure. The present statement supplies the analytic probe bounds; channel rigidity and compression bounds require their own channel and port hypotheses.")),
            new DocumentBlock.DisplayFormula(FiveModeStatement()),
            TwoSettingApplication()));

    private static DocumentBlock TwoSettingApplication() => new DocumentBlock.Section(
        H("Application to the actual two-setting channel and compression port"),
        Blocks(
            Paragraph(Text("Keep the mode order (N,2,3,5,25). Let K be the real symmetric adjacency matrix with undirected edges N-2, N-3, N-5, 2-25, and 5-25, each of weight one. Set D=diag(1,i,i,i,1), U(t)=exp(-itK), O(t)=exp(tA), and W(t)=ofReal(O(t)), where ofReal acts entrywise. The displayed A satisfies D adjoint times (-iK) times D = A. Thus D adjoint times U(t) times D = W(t) for every real t. Conjugation by D and its adjoint gives mutually inverse canonical CPTP maps on all complex density states. Because D is diagonal, this passive coordinate change preserves every mode probability.")),
            new DocumentBlock.DisplayFormula(Disp(Eq(
                Mul(Mul(Call("adjoint", F.Id("D")), Call("U", F.Id("t"))), F.Id("D")),
                Call("W", F.Id("t"))))),
            Paragraph(Text("For each of the two nonnegative waits t=0 and t=2/3, use every mode outcome s. With Pi_s=e_s e_s adjoint, the physical effects are U(t) adjoint times Pi_s times U(t); they are Hermitian idempotents and sum to identity. Their passive-frame representatives are W(t) adjoint times Pi_s times W(t)=ofReal(O(t) transpose times Pi_s times O(t)). For a physical density D rho D adjoint, their probabilities equal p_t(rho)_s=(W(t) rho W(t) adjoint)_{ss}, with rho ranging over all complex density matrices. In particular W(0)=I, and the pulled-back N effect at wait 2/3 is the rank-one projection of v=ofReal(O(2/3) transpose e_N).")),
            Paragraph(Text("The preceding analytic remainder calculation gives sum_j |v_j|^2=1 and |v_j|^2>1/8 for all five coordinates. The five probes (v,e_2,e_3,e_5,e_25) are unit vectors. The four coordinate probes are mutually orthogonal, and v has nonzero overlap with each one, so their nonorthogonality graph is exactly a connected four-spoke star. They span the entire complex five-dimensional space: the nonzero N coordinate of v recovers the omitted e_N direction.")),
            Paragraph(Text("Suppose a canonical CPTP endomorphism T preserves all outcome probabilities at both actual settings for every complex density input. It then preserves the probabilities of these five probes. Apply connected_probability_preserving_identity from "),
                Ref("D5/B/S3/Quantum/Reduction/ProbeComponentRigidity"),
                Text(" through the canonical finite Kraus representation. It follows that T(X)=X for every complex matrix X. The conclusion uses the complete density-input hypothesis, not a finite sample of calibration states.")),
            Paragraph(Text("Let q be any natural number, let F be any finite classical flag carrier, and let E:M_5(C) to M_(F times Fin q)(C) and R in the reverse direction be canonical CPTP maps. Require E to have classical block-diagonal output on every matrix input. Use the same E and R at both settings; flag probabilities may depend on the input, and F has no uniform cardinality bound. Exact preservation implies 5<=q by canonical_flag_port_lower_bound from "),
                Ref("D5/B/S3/Quantum/Reduction/CanonicalFlagCompression"),
                Text(" because the connected component of the five probes has dimension five. All input-dependent quantum information passes through Fin q.")),
            Paragraph(Text("For the quantitative statement, define epsilon(E,R) as the supremum over all complex density inputs of the maximum of the two total-variation errors, at waits 0 and 2/3, between the input and the common composite R composed with E. Total variation is half the sum of the five absolute probability differences. Canonical_flag_port_factorization supplies a normalized same-flag Kraus port with identical composite action on every matrix. Its encoder branch index is (F times Fin q) times Fin 5 and its decoder branch index is Fin 5 times (F times Fin q). Reading the same fields as a SparseProbePortBound.Port only reorders finite sums.")),
            new DocumentBlock.DisplayFormula(Disp(Eq(Call("epsilon", F.Id("E"), F.Id("R")),
                Call("sSup", new Formula.SetBuilder(Call("max",
                    Call("TV", Call("p", D(0), Rho), Call("p", D(0), Call("compose", F.Id("R"), F.Id("E"), Rho))),
                    Call("TV", Call("p", Rat(D(2), D(3)), Rho), Call("p", Rat(D(2), D(3)), Call("compose", F.Id("R"), F.Id("E"), Rho)))),
                    Rho, Call("DensityState", Call("Fin", D(5)))))))),
            Paragraph(Text("Apply sparse_probe_port_bound from "),
                Ref("D5/B/S3/Quantum/QuantumChannels/SparseProbePortBound"),
                Text(" with d=5, U=W(2/3), r=N=0, and mu=1/8. The row condition U_{N,j}=conj(v_j), unitarity, unit norm, and the pointwise support bound are supplied by the preceding exact calculation. The quantitative argument uses six survival tests: all five coordinate inputs and v. It gives the following uniform bound for every allowed canonical port with 1<=q<=5.")),
            new DocumentBlock.DisplayFormula(Disp(Le(Rat(
                new Formula.Binary(D(5), FormulaBinaryOperator.Subtract, F.Id("q")), D(1,0,2)),
                Call("epsilon", F.Id("E"), F.Id("R"))))),
            Paragraph(Text("Indeed mu(5-q)/((2+mu)(5+1))=(5-q)/102. Let C_q be the set of these epsilon(E,R) over all finite F and allowed canonical E,R. This set is nonempty for every positive q: coordinate measurement followed by storage of the outcome in the classical flag and preparation through one fixed quantum coordinate gives a normalized port. The uniform bound therefore passes to inf C_q. At q=5, a single-flag identity encoder and decoder attain zero error, so inf C_5=0 and the exact minimum coherent dimension is five. The same lower bound and attained-zero conclusion hold for the supplier's finite dependent-family Kraus-port error set.")),
            new DocumentBlock.DisplayFormula(Disp(And(
                Le(Rat(new Formula.Binary(D(5), FormulaBinaryOperator.Subtract, F.Id("q")), D(1,0,2)),
                    Call("infCanonicalErrors", F.Id("q"))),
                Eq(Call("infCanonicalErrors", D(5)), D(0))))),
            Paragraph(Text("These are composed applications of the analytic remainder calculation, connected-probe rigidity, canonical flagged-port factorization, and sparse-probe estimate. They assert neither optimality of the lower bound for q<5 nor a physical calibration theorem. The passive frame does not add an operation to the two-wait menu. The cited suppliers retain their own assumptions and literature attribution."))));

    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Rat(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula FiveModeStatement()
    {
        Formula o = Call("actualFiveModeExponential", Rat(D(2), D(3)));
        Formula s = Call("actualFiveModeTaylor", Rat(D(2), D(3)), D(1,3));
        Formula v = Call("mulVec", Call("transpose", o), Call("basisVector", D(5), D(0)));
        Formula j = F.Id("j"), entry = Call("coordinate", v, j);
        Formula all(Formula p) => new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("j"), Call("Fin", D(5)), p);
        Formula tail = Rat(Mul(Rat(D(7), D(6)), new Formula.Power(D(2), D(1,3))), Call("factorial", D(1,3)));
        return Disp(And(Eq(Mul(Call("transpose", o), o), D(1)),
            And(Eq(Mul(o, Call("transpose", o)), D(1)),
            And(Le(new Formula.Norm(new Formula.Binary(o, FormulaBinaryOperator.Subtract, s)), tail),
            And(all(Lt(Rat(D(9), D(2,5)), new Formula.Absolute(entry))),
            And(all(Lt(Rat(D(1), D(8)), new Formula.Power(entry, D(2)))),
                And(Lt(Rat(D(1), D(8)), Call("minimumSquaredCoordinate", v)),
                Eq(Call("squareSum", v), D(1)))))))));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation;

internal sealed class TransmissivityTwoPointProbeRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/zhou2023transmissivity");
    private const string Quote = "For the two-point prior PDF (15), we verify that for integer n̄ the optimal state is the Fock state with the same photon number. For real n̄, our numerical results support the conjecture that the optimal state has the form of the state (27), up to a phase, i.e., |Φ′ₙ̄⟩ = e^{iφn̂}|Φₙ̄⟩.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A vacuum–two-photon superposition has strictly smaller Bayesian transmissivity error than every phased in-between state at mean photon number one half, for an equiprobable two-point prior.",
        H("In-between states do not always minimize Bayesian transmissivity error"),
        Blocks(
            Node("meanPhoton", "Mean photon number", MeanFormula(),
                "Equations (30)–(32), p. 4: psi gives complex Fock coefficients on Fin(N+1). val is the natural-number value of a finite index, toReal casts it to the reals, and normSq is the squared complex modulus. Hilbert normalization is norm(toLp(2,psi))=1, meaning the Euclidean L2 norm rather than the sup norm of a function space."),
            Node("outputState", "Pure-loss output", OutputFormula(),
                "The pure-loss channel sends |n> to sqrt(choose(n,l) tau^(n-l) (1-tau)^l)|n-l> in Kraus branch l. The reused amplitudeKraus(l,f) has entries ofReal(sqrt(choose(n,l)) sqrt(1-f)^(n-l) sqrt(f)^l) at row n-l and column n. Here f=1-tau, so on 0<=tau<=1 its coefficient is exactly the source coefficient. Natural subtraction is truncated subtraction. rankOneDensity(psi)=vecMulVec(psi,star(psi)) is the input outer product; adjoint is conjugate transpose. The finite sum contains all nonzero Kraus branches for a finite Fock support. The formula defines the channel output. For natural n and l and admissible tau, the source coefficient equals the factored coefficient of the frozen owner as displayed below.", proseFormula: CoefficientFormula()),
            Node("momentState", "Two-point moment operators", MomentFormula(),
                "Equations (13) and (15), p. 3: P(tau)=q delta(tau-tau0)+(1-q) delta(tau-tau1), where 0<=q<=1. momentState(k) is Gamma_k with the real prior weights cast to complex scalars. smul denotes scalar multiplication of a matrix."),
            Node("finitePOVM", "Finite positive operator valued measurements", PovmFormula(),
                "The effects are positive semidefinite matrices on the output Fock span, and their sum is the identity matrix. The outcome count m may be any natural number, and the estimates in the risk below are real numbers."),
            Node("bayesianRisk", "Bayesian squared-error risk", RiskFormula(),
                "Equations (10)–(13), pp. 2–3: the finite measurement risk is sum_k Re tr(E_k (x_k^2 Gamma_0-2 x_k Gamma_1+Gamma_2)). Re extracts the real part of the complex trace. The real estimate coefficients are cast by ofReal before matrix scalar multiplication."),
            Node("MMSE", "Minimum mean square error", MmseFormula(),
                "MMSE is the real infimum of the risks of all finite POVMs and all real estimates on the finite output span. Identifying this finite-outcome quantity with the source's MMSE over arbitrary measurements requires the following compression argument: an output supported on a finite span has identical statistics for a full-space effect E and its compression P E P; compressing a POVM preserves completeness on the span. A finite POVM on the span extends by assigning the orthogonal complement to one outcome. ASSUMED-UNVERIFIED: this compression argument and the equality with the arbitrary-outcome source MMSE are not kernel-checked in this module. The Lean lower bound and spectral attainment concern finite POVMs only. The finite-dimensional definition is extended to raw parameters and unnormalised vectors, but the claim uses only admissible parameters and normalised inputs."),
            Node("inBetween", "Phased in-between Fock states", InBetweenFormula(),
                "Section V, p. 4: \"For this case, we provide numerical evidence that the optimal state has the form,\" followed by (27) |Phi_nbar>=|a(nbar)| |ceil(nbar)-1>+|c(nbar)| |ceil(nbar)>, (28) |c(nbar)|=sqrt(1-ceil(nbar)+nbar), and (29) |a(nbar)|=sqrt(1-|c(nbar)|^2). The source says: \"We refer to the state of Eq. (27) as in-between state as it is a superposition of the two nearest Fock states for a given n̄ and it reverts to a Fock state when n̄ is an integer.\" Equation (33) applies exp(i phi n-hat). ceilNat is the natural ceiling; for the positive nbar in the claim it is the source ceiling. NatSub is natural truncated subtraction, and ComplexI is the imaginary unit. The conditional order and extension outside positive nbar match the Lean definition."),
            Node("claim", "Non-integer-energy optimality conjecture", ClaimFormula(),
                "Section V, arXiv v1 PDF p. 4: \"" + Quote + "\" The prior parameters range over [0,1]; nbar is positive; N is any finite Fock cutoff. The psi input has Euclidean norm one and meanPhoton(psi)=nbar. The encoding says that some phased in-between state has finite-POVM MMSE no greater than each competing input. Each state's MMSE is computed on its own finite output span. Identification with the source's arbitrary-measurement optimum requires the compression argument stated above and a reduction from arbitrary outcomes to finite outcomes; that bridge is ASSUMED-UNVERIFIED and not kernel-checked here."),
            Describe.Lean(DescribeId.Create("bmse-sqrt-power"),
                DeclarationHandle.Create(Prefix + "sqrt_power"), H("Square roots of nonnegative natural powers"),
                StatementSource.FromAuthor(Disp(All("t", Real(), Imp(LeqOf(D(0), F.Id("t")), All("k", Nat(), Eqn(Call("sqrt", Pow(F.Id("t"), F.Id("k"))), Pow(Call("sqrt", F.Id("t")), F.Id("k")))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For t nonnegative and natural k, sqrt(t^k)=sqrt(t)^k. The power factorization follows by induction using multiplicativity of the square root on nonnegative inputs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bmse-source-coefficient"),
                DeclarationHandle.Create(Prefix + "source_coefficient"), H("Factored pure-loss Kraus coefficient"),
                StatementSource.FromAuthor(Disp(All("n", Nat(), All("l", Nat(), All("tau", Real(), Imp(Call("mem", F.Id("tau"), Call("Icc", D(0), D(1))), Eqn(Call("sqrt", Mul(Mul(Cast(Call("choose", F.Id("n"), F.Id("l"))), Pow(F.Id("tau"), Call("NatSub", F.Id("n"), F.Id("l")))), Pow(Sub(D(1), F.Id("tau")), F.Id("l")))), Mul(Mul(Call("sqrt", Cast(Call("choose", F.Id("n"), F.Id("l")))), Pow(Call("sqrt", F.Id("tau")), Call("NatSub", F.Id("n"), F.Id("l")))), Pow(Call("sqrt", Sub(D(1), F.Id("tau"))), F.Id("l")))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For tau in [0,1], the source coefficient sqrt(choose(n,l) tau^(n-l) (1-tau)^l) equals sqrt(choose(n,l)) sqrt(tau)^(n-l) sqrt(1-tau)^l. Natural subtraction is truncated."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bmse-sourcekraus"),
                DeclarationHandle.Create(Prefix + "sourceKraus"), H("Source form of the pure-loss Kraus matrix"),
                StatementSource.FromAuthor(Disp(All("N", Nat(), All("l", Index(F.Id("N")), All("tau", Real(), Imp(Call("mem", F.Id("tau"), Call("Icc", D(0), D(1))), Eqn(Call("amplitudeKraus", F.Id("N"), F.Id("l"), Sub(D(1), F.Id("tau"))), Call("MatrixOf", Seq(F.Id("fun"), Sp, F.Id("r"), Sp, F.Id("c"), Sp, Colon, Sp, Index(F.Id("N")), Sp, Mapsto, Sp, Call("ite", Eqn(Add(Val(F.Id("r")), Val(F.Id("l"))), Val(F.Id("c"))), Call("ite", LeqOf(Val(F.Id("l")), Val(F.Id("c"))), C(Call("sqrt", Mul(Mul(Cast(Call("choose", Val(F.Id("c")), Val(F.Id("l")))), Pow(F.Id("tau"), Call("NatSub", Val(F.Id("c")), Val(F.Id("l"))))), Pow(Sub(D(1), F.Id("tau")), Val(F.Id("l")))))), D(0)), D(0))))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite cutoff N, Kraus index l and tau in [0,1], amplitudeKraus(l,1-tau) has the source coefficient at row r and column c when r.val+l.val=c.val and l.val<=c.val, and zero otherwise. Matrix.of turns the displayed entry function into a matrix."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bmse-moment-variance"),
                DeclarationHandle.Create(Prefix + "moment_variance"), H("Positive measurement moment variance"),
                StatementSource.FromAuthor(Disp(All("d", Nat(), All("m", Nat(), All("E", Func(Outcomes(F.Id("m")), Call("Matrix", Outcomes(F.Id("d")), Outcomes(F.Id("d")), Complex())), All("x", Estimates(F.Id("m")), Imp(And(All("k", Outcomes(F.Id("m")), Call("PosSemidef", At(F.Id("E"), F.Id("k")))), Eqn(SumOver("k", Outcomes(F.Id("m")), At(F.Id("E"), F.Id("k"))), D(1))), Call("PosSemidef", Sub(SumOver("k", Outcomes(F.Id("m")), Call("smul", C(Pow(At(F.Id("x"), F.Id("k")), D(2))), At(F.Id("E"), F.Id("k")))), Mul(SumOver("k", Outcomes(F.Id("m")), Call("smul", C(At(F.Id("x"), F.Id("k"))), At(F.Id("E"), F.Id("k")))), SumOver("k", Outcomes(F.Id("m")), Call("smul", C(At(F.Id("x"), F.Id("k"))), At(F.Id("E"), F.Id("k")))))))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive semidefinite effects summing to the identity and real estimates x, M2-M1 M1 is positive semidefinite, where M1=sum_k ofReal(x_k) E_k and M2=sum_k ofReal(x_k^2) E_k. The formula expands those two sums. The difference is the sum of the positive sandwiches (x_k I-M1)^H E_k (x_k I-M1)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bmse-risk-lower-bound"),
                DeclarationHandle.Create(Prefix + "risk_lower_bound"), H("Square-completion bound for every finite measurement"),
                StatementSource.FromAuthor(Disp(All("d", Nat(), All("m", Nat(), All("A", Call("Matrix", Outcomes(F.Id("d")), Outcomes(F.Id("d")), Complex()), All("C", Call("Matrix", Outcomes(F.Id("d")), Outcomes(F.Id("d")), Complex()), All("D", Call("Matrix", Outcomes(F.Id("d")), Outcomes(F.Id("d")), Complex()), All("B", Call("Matrix", Outcomes(F.Id("d")), Outcomes(F.Id("d")), Complex()), Imp(Call("PosSemidef", F.Id("A")), Imp(Call("IsHermitian", F.Id("B")), Imp(Eqn(Add(Mul(F.Id("A"), F.Id("B")), Mul(F.Id("B"), F.Id("A"))), Call("smul", C(D(2)), F.Id("C"))), All("E", Func(Outcomes(F.Id("m")), Call("Matrix", Outcomes(F.Id("d")), Outcomes(F.Id("d")), Complex())), All("x", Estimates(F.Id("m")), Imp(And(All("k", Outcomes(F.Id("m")), Call("PosSemidef", At(F.Id("E"), F.Id("k")))), Eqn(SumOver("k", Outcomes(F.Id("m")), At(F.Id("E"), F.Id("k"))), D(1))), LeqOf(Call("Re", Sub(Call("trace", F.Id("D")), Call("trace", Mul(F.Id("B"), F.Id("C"))))), SumOver("k", Outcomes(F.Id("m")), Call("Re", Call("trace", Mul(At(F.Id("E"), F.Id("k")), Add(Sub(Call("smul", C(Pow(At(F.Id("x"), F.Id("k")), D(2))), F.Id("A")), Call("smul", C(Mul(D(2), At(F.Id("x"), F.Id("k")))), F.Id("C"))), F.Id("D"))))))))))))))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let A,C,D,B be arbitrary complex square matrices of dimension d. If A is positive semidefinite, B Hermitian and A B+B A=2 C, every finite POVM with real estimates has quadratic risk at least Re(trace(D)-trace(B C)). The positive measurement variance and the positive square (M1-B)^2 yield the bound after trace square completion."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bmse-spectral-attainment"),
                DeclarationHandle.Create(Prefix + "spectral_attainment"), H("Spectral measurement attains the trace certificate"),
                StatementSource.FromAuthor(Disp(All("d", Nat(), All("A", Call("Matrix", Outcomes(F.Id("d")), Outcomes(F.Id("d")), Complex()), All("C", Call("Matrix", Outcomes(F.Id("d")), Outcomes(F.Id("d")), Complex()), All("D", Call("Matrix", Outcomes(F.Id("d")), Outcomes(F.Id("d")), Complex()), All("B", Call("Matrix", Outcomes(F.Id("d")), Outcomes(F.Id("d")), Complex()), Imp(Call("IsHermitian", F.Id("B")), Imp(Eqn(Add(Mul(F.Id("A"), F.Id("B")), Mul(F.Id("B"), F.Id("A"))), Call("smul", C(D(2)), F.Id("C"))), Ex("E", Func(Outcomes(F.Id("d")), Call("Matrix", Outcomes(F.Id("d")), Outcomes(F.Id("d")), Complex())), Ex("x", Estimates(F.Id("d")), And(And(All("k", Outcomes(F.Id("d")), Call("PosSemidef", At(F.Id("E"), F.Id("k")))), Eqn(SumOver("k", Outcomes(F.Id("d")), At(F.Id("E"), F.Id("k"))), D(1))), Eqn(SumOver("k", Outcomes(F.Id("d")), Call("Re", Call("trace", Mul(At(F.Id("E"), F.Id("k")), Add(Sub(Call("smul", C(Pow(At(F.Id("x"), F.Id("k")), D(2))), F.Id("A")), Call("smul", C(Mul(D(2), At(F.Id("x"), F.Id("k")))), F.Id("C"))), F.Id("D")))))), Call("Re", Sub(Call("trace", F.Id("D")), Call("trace", Mul(F.Id("B"), F.Id("C")))))))))))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let A,C,D,B be arbitrary complex square matrices of dimension d. If B is Hermitian and A B+B A=2 C, its spectral projections form a d-outcome POVM. Taking its real eigenvalues as estimates gives quadratic risk exactly Re(trace(D)-trace(B C)). No positivity hypothesis on A is required for this attainment identity."))), DescribeRole.Theorem),
            Node("result", "Strict error advantage of a nonadjacent Fock superposition", Disp(new Formula.Not(F.Id("claim"))),
                "Take q=1/2, tau0=4/9, tau1=1 and nbar=1/2. Every in-between phase has MMSE 1625/23976, whereas psi=(sqrt(3)/2)|0>+(1/2)|2> has MMSE 110575/1674432, with positive gap 107725/61953984. Its Hilbert norm is one and its mean photon number is one half. For any finite POVM, the operator variance M2-M1^2 is a sum of positive semidefinite sandwiches. If Gamma0 B+B Gamma0=2 Gamma1, completing the square gives risk>=Re tr(Gamma2-B Gamma1). The phased two-dimensional certificate is [[787,145 exp(-i phi)],[145 exp(i phi),937]]/1332. The competitor certificate is [[62971,0,4293 sqrt(3)],[0,41344,0],[4293 sqrt(3),0,68965]]/93024. Both solve the Sylvester equation for the channel outputs. Spectral projections of each Hermitian certificate, with its eigenvalues as estimates, attain its lower bound. The rational comparison refutes the conjecture. It does not assert that the competitor is globally optimal, or settle the beta-prior conjecture.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhou-bash-guha-gagatsos-2023-transmissivity-in-between-probe-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Definition, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? resolution = null, Formula? proseFormula = null) => Describe.Lean(
            DescribeId.Create("bmse-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance ?? AssessedProvenance.FromLiterature(Source),
            proseFormula is null ? Blocks(Paragraph(Text(prose))) :
                Blocks(Paragraph(Text(prose)), Paragraph(Math(proseFormula))), role, resolution);

    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. xs]);
    private static Formula At(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula All(string v, Formula type, Formula body) => Seq(Forall, Sp, F.Id(v), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string v, Formula type, Formula body) => Seq(Exists, Sp, F.Id(v), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula LeqOf(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula LtOf(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula IffOf(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(Parenthesized(x), FormulaBinaryOperator.Multiply, Parenthesized(y));
    private static Formula Pow(Formula x, Formula y) => Seq(Parenthesized(x), Caret, Grp(y));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Index(Formula cutoff) => Call("Fin", Add(cutoff, D(1)));
    private static Formula Outcomes(Formula m) => Call("Fin", m);
    private static Formula Func(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula Ket(Formula cutoff) => Func(Index(cutoff), Complex());
    private static Formula State(Formula cutoff) => Call("Matrix", Index(cutoff), Index(cutoff), Complex());
    private static Formula Effects(Formula cutoff, Formula m) => Func(Outcomes(m), State(cutoff));
    private static Formula Estimates(Formula m) => Func(Outcomes(m), Real());
    private static Formula Cast(Formula x) => Call("toReal", x);
    private static Formula C(Formula x) => Call("ofReal", x);
    private static Formula Val(Formula n) => Call("val", n);
    private static Formula SumOver(string i, Formula domain, Formula body) => Seq(Sum, Underscore,
        Grp(F.Id(i), Sp, Colon, Sp, domain), Sp, Parenthesized(body));
    private static Formula N => F.Id("N");
    private static Formula M => F.Id("m");
    private static Formula Q => F.Id("q");
    private static Formula T0 => F.Id("tau0");
    private static Formula T1 => F.Id("tau1");
    private static Formula P => F.Id("psi");
    private static Formula E => F.Id("E");
    private static Formula X => F.Id("x");
    private static Formula K => F.Id("k");
    private static Formula Nb => F.Id("nbar");
    private static Formula Phi => F.Id("phi");
    private static Formula Ceiling => Call("ceilNat", Nb);
    private static Formula Moment(Formula k) => Call("momentState", N, Q, T0, T1, P, k);
    private static Formula Risk => Call("bayesianRisk", N, M, Q, T0, T1, P, E, X);
    private static Formula PriorBind(Formula body) => All("q", Real(), All("tau0", Real(), All("tau1", Real(), body)));
    private static Formula InUnit(Formula x) => Call("mem", x, Call("Icc", D(0), D(1)));

    private static Formula MeanFormula() => Disp(All("N", Nat(), All("psi", Ket(N),
        Eqn(Call("meanPhoton", N, P), SumOver("n", Index(N),
            Mul(Cast(Val(F.Id("n"))), Call("normSq", At(P, F.Id("n")))))))));

    private static Formula OutputFormula()
    {
        Formula t=F.Id("tau"), l=F.Id("l");
        Formula a=Call("amplitudeKraus", N, l, Sub(D(1),t));
        return Disp(All("N",Nat(),All("tau",Real(),All("psi",Ket(N),
            Eqn(Call("outputState",N,t,P),SumOver("l",Index(N),
                Mul(Mul(a,Call("rankOneDensity",P)),Call("adjoint",a))))))));
    }

    private static Formula CoefficientFormula()
    {
        Formula n=F.Id("n"), l=F.Id("l"), t=F.Id("tau");
        Formula choose=Call("choose",n,l), exponent=Call("NatSub",n,l);
        Formula source=Seq(Sqrt,Grp(Mul(Mul(Cast(choose),Pow(t,exponent)),Pow(Sub(D(1),t),l))));
        Formula owner=Mul(Mul(Seq(Sqrt,Grp(Cast(choose))),Pow(Seq(Sqrt,Grp(t)),exponent)),
            Pow(Seq(Sqrt,Grp(Sub(D(1),t))),l));
        return Disp(All("n",Nat(),All("l",Nat(),All("tau",Real(),
            Imp(InUnit(t),Eqn(source,owner))))));
    }

    private static Formula MomentFormula() => Disp(All("N",Nat(),PriorBind(All("psi",Ket(N),All("k",Nat(),
        Eqn(Moment(K),Add(Call("smul",C(Mul(Q,Pow(T0,K))),Call("outputState",N,T0,P)),
            Call("smul",C(Mul(Sub(D(1),Q),Pow(T1,K))),Call("outputState",N,T1,P)))))))));

    private static Formula PovmFormula() => Disp(All("N",Nat(),All("m",Nat(),All("E",Effects(N,M),
        IffOf(Call("finitePOVM",N,M,E),And(All("k",Outcomes(M),Call("PosSemidef",At(E,K))),
            Eqn(SumOver("k",Outcomes(M),At(E,K)),D(1))))))));

    private static Formula RiskFormula()
    {
        Formula x=At(X,K);
        Formula expression=Add(Sub(Call("smul",C(Pow(x,D(2))),Moment(D(0))),
            Call("smul",C(Mul(D(2),x)),Moment(D(1)))),Moment(D(2)));
        return Disp(All("N",Nat(),All("m",Nat(),PriorBind(All("psi",Ket(N),All("E",Effects(N,M),All("x",Estimates(M),
            Eqn(Risk,SumOver("k",Outcomes(M),Call("Re",Call("trace",Mul(At(E,K),expression))))))))))));
    }

    private static Formula MmseFormula()
    {
        Formula r=F.Id("r");
        Formula predicate=Ex("m",Nat(),Ex("E",Effects(N,M),Ex("x",Estimates(M),
            And(Call("finitePOVM",N,M,E),Eqn(r,Risk)))));
        Formula set=Seq(OpenBrace,r,Sp,Colon,Sp,Real(),Sp,Mid,Sp,predicate,CloseBrace);
        return Disp(All("N",Nat(),PriorBind(All("psi",Ket(N),Eqn(Call("MMSE",N,Q,T0,T1,P),Call("sInf",set))))));
    }

    private static Formula InBetweenFormula()
    {
        Formula n=F.Id("n");
        Formula c=Call("sqrt",Add(Sub(D(1),Cast(Ceiling)),Nb));
        Formula a=Call("sqrt",Sub(D(1),Pow(c,D(2))));
        Formula value=Call("ite",Eqn(Val(n),Call("NatSub",Ceiling,D(1))),C(a),
            Call("ite",Eqn(Val(n),Ceiling),C(c),D(0)));
        Formula phase=Call("exp",Mul(Call("ComplexI"),C(Mul(Phi,Cast(Val(n))))));
        return Disp(All("nbar",Real(),All("phi",Real(),All("n",Index(Ceiling),
            Eqn(At(Call("inBetween",Nb,Phi),n),Mul(phase,value))))));
    }

    private static Formula ClaimFormula()
    {
        Formula normal=Eqn(Call("norm",Call("toLp",D(2),P)),D(1));
        Formula choice=Ex("phi",Real(),LeqOf(Call("MMSE",Ceiling,Q,T0,T1,Call("inBetween",Nb,Phi)),
            Call("MMSE",N,Q,T0,T1,P)));
        Formula competitors=All("N",Nat(),All("psi",Ket(N),Imp(normal,
            Imp(Eqn(Call("meanPhoton",N,P),Nb),choice))));
        return Disp(IffOf(F.Id("claim"),PriorBind(All("nbar",Real(),Imp(InUnit(Q),Imp(InUnit(T0),
            Imp(InUnit(T1),Imp(LtOf(D(0),Nb),competitors))))))));
    }
}

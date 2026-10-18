using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class HypercubeMarkedPoissonAsymptoticsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/HypercubeMarkedPoissonAsymptotics.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Marked Poisson Asymptotics on the Original Hypercube", H("Marked Poisson Asymptotics on the Original Hypercube"), Blocks(
        Describe.Lean(DescribeId.Create("hypercubemarkedhistory-cube"), DeclarationHandle.Create(Module + "Cube"),
            H("Cube"), StatementSource.FromAuthor(Disp(HCQ("d", HCV("Nat"), HCEqn(HCCall("Cube", HCV("d")), HCFn(HCFinF(HCAdd(HCV("d"), HCN(1))), HCCall("IntegerUnits")))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The original sign hypercube has dimension d+1, so each native parity class has M=2^d states. IntegerUnits is the two-element group of units of the integers, consisting of 1 and -1."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("hypercubemarkedhistory-cubeequiv"), DeclarationHandle.Create(Module + "cubeEquiv"),
            H("cubeEquiv"), StatementSource.FromAuthor(Disp(HCQ("d", HCV("Nat"), HCEqn(HCCall("cubeEquiv", HCV("d")), HCCall("parityTailBijection", HCV("d")))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The parity-tail bijection sends x to its product parity and the index of its last d coordinates. The tail index is the finite enumeration of the 2^d sign tails. Positive parity selects inl and negative parity selects inr. The inverse recovers the first sign as the requested parity times the product of the tail signs."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("hypercubemarkedhistory-positiveequiv"), DeclarationHandle.Create(Module + "positiveEquiv"),
            H("positiveEquiv"), StatementSource.FromAuthor(Disp(HCQ("d", HCV("Nat"), HCQ("x", HCCall("PositiveCube", HCV("d")), HCEqn(HCCall("cubeEquiv", HCV("d"), HCCall("value", HCV("x"))), HCCall("inl", HCCall("positiveEquiv", HCV("d"), HCV("x")))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("PositiveCube(d) is the subtype of Cube(d) with product parity 1. The displayed characterization fixes an equivalence to Fin(2^d), without an assumed transport map."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("hypercubemarkedhistory-cubesupport"), DeclarationHandle.Create(Module + "CubeSupport"),
            H("CubeSupport"), StatementSource.FromAuthor(Disp(HCQ("d q", HCV("Nat"), HCEqn(HCCall("CubeSupport", HCV("d"), HCV("q")), HCCall("fixedCardinalitySubsets", HCCall("PositiveCube", HCV("d")), HCV("q")))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A source support is an arbitrary q-element finite subset of the positive parity class."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("hypercubemarkedhistory-cubesupportequiv"), DeclarationHandle.Create(Module + "cubeSupportEquiv"),
            H("cubeSupportEquiv"), StatementSource.FromAuthor(Disp(HCQ("d q", HCV("Nat"), HCQ("S", HCCall("CubeSupport", HCV("d"), HCV("q")), HCEqn(HCCall("cubeSupportEquiv", HCV("d"), HCV("q"), HCV("S")), HCCall("supportImage", HCCall("positiveEquiv", HCV("d")), HCV("S"))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("supportImage maps every member of S through positiveEquiv. Its inverse maps through the inverse equivalence, preserving cardinality. All native and all original supports occur."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("hypercubemarkedhistory-cubeobs"), DeclarationHandle.Create(Module + "CubeObs"),
            H("CubeObs"), StatementSource.FromAuthor(Disp(HCQ("d s", HCV("Nat"), HCQ("e", HCCall("Experiment"), HCEqn(HCCall("CubeObs", HCV("d"), HCV("s"), HCV("e")), HCCall("cubeHistoryCarrier", HCV("d"), HCV("s"), HCV("e"))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For pairs, cubeHistoryCarrier is Fin(s) -> Cube(d) x Cube(d). For paths it is Fin(s+1) -> Cube(d)."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("hypercubemarkedhistory-historyequiv"), DeclarationHandle.Create(Module + "historyEquiv"),
            H("historyEquiv"), StatementSource.FromAuthor(Disp(HCQ("d s", HCV("Nat"), HCQ("e", HCCall("Experiment"), HCEqn(HCCall("historyEquiv", HCV("d"), HCV("s"), HCV("e")), HCCall("endpointwiseEquivalence", HCCall("cubeEquiv", HCV("d")), HCV("s"), HCV("e"))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Apply cubeEquiv to both endpoints of every independent pair, or to every state of a complete continuous path. This preserves ordered edges."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("hypercubemarkedhistory-cubeprofile"), DeclarationHandle.Create(Module + "cubeProfile"),
            H("cubeProfile"), StatementSource.FromAuthor(Disp(HCCubeData(HCQ("x", HCCall("Cube", HCV("d")), HCEqn(HCCall("cubeProfile", HCV("r"), HCV("S"), HCV("x")), HCCall("supportedProfile", HCV("r"), HCV("S"), HCV("x"))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("supportedProfile is r on S, minus r q/(2^d-q) on its positive complement, and zero on the negative class. The denominator uses the natural difference."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("hypercubemarkedhistory-cubekernel"), DeclarationHandle.Create(Module + "cubeKernel"),
            H("cubeKernel"), StatementSource.FromAuthor(Disp(HCCubeData(HCQ("reverse", HCCall("Bool"), HCQ("x y", HCCall("Cube", HCV("d")), HCEqn(HCCall("cubeKernel", HCV("r"), HCV("S"), HCV("reverse"), HCV("x"), HCV("y")), HCCall("orientedParityKernel", HCV("r"), HCV("S"), HCV("reverse"), HCV("x"), HCV("y")))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The forward kernel is (1+cubeProfile(r,S,x) parity(y))/2^(d+1). The reverse kernel interchanges x and y before evaluating this expression."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("hypercubemarkedhistory-cubeprobability"), DeclarationHandle.Create(Module + "cubeProbability"),
            H("cubeProbability"), StatementSource.FromAuthor(Disp(HCCubeHistoryData(HCQ("o", HCCall("CubeObs", HCV("d"), HCV("s"), HCV("e")), HCEqn(HCCall("cubeProbability", HCV("r"), HCV("S"), HCV("reverse"), HCV("e"), HCV("o")), HCCall("cubeHistoryMass", HCV("d"), HCV("r"), HCV("S"), HCV("reverse"), HCV("e"), HCV("o"))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For pairs this is the product of 2^(-(d+1)) times cubeKernel at each ordered pair. For paths it is 2^(-(d+1)) times the consecutive kernel product. The same S is used for every edge."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("hypercubemarkedhistory-cubecount"), DeclarationHandle.Create(Module + "cubeCount"),
            H("cubeCount"), StatementSource.FromAuthor(Disp(HCQ("d s", HCV("Nat"), HCQ("e", HCCall("Experiment"), HCQ("o", HCCall("CubeObs", HCV("d"), HCV("s"), HCV("e")), HCQ("x", HCCall("Cube", HCV("d")), HCQ("sigma", HCV("Real"), HCEqn(HCCall("cubeCount", HCV("e"), HCV("o"), HCV("x"), HCV("sigma")), HCCall("markedCubeEdgeCount", HCV("e"), HCV("o"), HCV("x"), HCV("sigma")))))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Count observed ordered edges departing from exactly x with destination parity sigma. Path endpoints are consecutive states; pair endpoints belong to the same sampled pair."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("hypercubemarkedhistory-hypercube-history-transport"), DeclarationHandle.Create(Module + "hypercube_history_transport"),
            H("hypercube history transport"), StatementSource.FromAuthor(Disp(HCTransport())), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("All five clauses concern the same fixed original support, direction and experiment. Sstar denotes cubeSupportEquiv(d,q,S), H denotes historyEquiv(d,s,e), and v denotes cubeEquiv(d). nativeKernel and nativeMass select transition/probability forward and transposed transition/reverseProbability backward. Every native positive row i and every real destination parity sigma occurs in the count clause. The last clause ranges over every predicate E on complete native histories and sums exactly corresponding source history masses."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("hypercube-marked-ell"), DeclarationHandle.Create(Module + "ell"),
            H("Logarithmic scale"), StatementSource.FromAuthor(Disp(Q("d", V("Nat"), EqF(Call("ell", V("d")), Call("log", M))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The index d denotes a cube of dimension d+1. Its parity classes each have M=2^d states, n=2M, and ell=log M. Letting d tend to infinity has exactly the original positive-dimension asymptotic meaning."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("hypercube-marked-observation-scale"), DeclarationHandle.Create(Module + "observationScale"),
            H("Exact observation scale"), StatementSource.FromAuthor(Disp(Q("s", Fn(V("Nat"), V("Nat")), Q("d", V("Nat"), EqF(Call("observationScale", V("s"), V("d")), Div(Call("s", V("d")), Mul(N(2), M))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The observation length s(d) is any natural number. L=s(d)/(2M) is real; the definitions and conclusions impose no divisibility or rounding of the observation length."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("hypercube-marked-source-regime"), DeclarationHandle.Create(Module + "SourceRegime"),
            H("Original asymptotic hypotheses"), StatementSource.FromAuthor(Disp(Q("r beta alpha", V("Real"), Q("q s", Fn(V("Nat"), V("Nat")), Regime())))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Fix 0<r<1, 1/2<beta<1 and alpha>0. timeToLogRatioSequence(s) is the sequence d mapped to observationScale(s,d)/ell(d). There is a real sequence delta(d) tending to zero such that q(d)=M^(1-beta+delta(d)) eventually, and L/ell tends to alpha. Both q and s are natural-valued sequences. No convergence rate is imposed. Positivity of q, q<M, small compensation, L>=1 and L/M tending to zero are consequences, rather than additional source assumptions."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("hypercube-marked-source-count-vector"), DeclarationHandle.Create(Module + "sourceCountVector"),
            H("Actual marked count vector"), StatementSource.FromAuthor(Disp(Q("d s k", V("Nat"), Q("e", Call("Experiment"), Q("m", Call("PositiveMarks", V("d"), V("k")), Q("o", Call("CubeObs", V("d"), V("s"), V("e")), EqF(Call("sourceCountVector", V("e"), V("m"), V("o")), Call("pairOfParityDepartureCounts", V("e"), V("m"), V("o"))))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The coordinate type is Fin(k) plus Fin(k). The first copy counts departures from the selected positive-parity state m(j) to positive parity; the second counts departures to negative parity. All coordinates use the same complete history o. Any k-element set of positive states admits an injective enumeration of this form."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("hypercube-marked-source-event"), DeclarationHandle.Create(Module + "sourceEvent"),
            H("Actual count event mass"), StatementSource.FromAuthor(Disp(CountData(Q("e", Call("Experiment"), Q("E", Call("Set", Counts), EqF(Call("sourceEvent", V("r"), V("S"), V("reverse"), V("m"), V("s"), V("e"), V("E")), Call("sumHistoryMassOnCountEvent", V("r"), V("S"), V("reverse"), V("m"), V("s"), V("e"), V("E")))))))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Sum the original cube history mass over precisely those histories whose entire marked count vector lies in E. The direction is the original kernel or its actual transpose. The experiment is independent stationary adjacent pairs or a continuous path with a uniform start. The true support S is fixed throughout each history."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("hypercube-marked-source-rates"), DeclarationHandle.Create(Module + "sourceRates"),
            H("Exact directional Poisson means"), StatementSource.FromAuthor(Disp(CountData(Rates()))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The displayed real values hold in the source regime at all sufficiently large dimensions. Globally sourceRates uses the nonnegative part of each displayed expression. The local theorem includes ExactDirectionalMeans, which proves these expressions equal the actual one-edge probabilities multiplied by the exact integer s. The comparison law is the genuine product of all 2k Poisson measures at these means."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("hypercube-marked-exact-directional-means"), DeclarationHandle.Create(Module + "ExactDirectionalMeans"),
            H("One-edge probabilities and exact means"), StatementSource.FromAuthor(Disp(CountData(EqF(Call("ExactDirectionalMeans", V("r"), V("S"), V("reverse"), V("m"), V("s")), ExactMeans())))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For each j and destination parity sigma, sum n^(-1)K(m(j),y) over all original cube destinations y of parity sigma. This probability is (1+sigma b(m(j)))/(2n) forward and 1/(2n) backward. The corresponding sourceRates coordinate is s times that probability. The reverse calculation uses the zero sum of the compensated profile on the positive class; it does not assert independence along a reverse path."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("hypercube-marked-local-asymptotics"), DeclarationHandle.Create(Module + "hypercube_marked_local_asymptotics"),
            H("Uniform relative local masses"), StatementSource.FromAuthor(Disp(Local())), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For fixed r, alpha and C>0, choose A>0 before beta and the natural support/time sequences, before the eventual dimension and before all true supports, distinct one or two marked positive states, directions, experiments and nonnegative count tuples. Every tuple of total count at most C ell has strictly positive comparison mass and relative error at most A ell^(k+1)/n. The all-zero tuple and rare point masses remain included. ExactDirectionalMeans is part of the conclusion. The proof uses the actual cube/native history correspondence, the directional signed PGF estimates, and the common coefficient normalization at exact real means."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("hypercube-marked-tail-event-asymptotics"), DeclarationHandle.Create(Module + "hypercube_marked_tail_event_asymptotics"),
            H("Every-D tails and all count events"), StatementSource.FromAuthor(Disp(TailEvents())), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For each fixed D>0 choose the cutoff C=(2(alpha+1)+D+2)/log 2 and a positive relative constant A before beta and the support/time sequences, before the eventual dimension and all supports, marks, directions, experiments and events. The actual and product-Poisson tails above C ell sum to at most M^(-D). Every count event E has absolute discrepancy at most A ell^(k+1)/n times its comparison probability plus M^(-D). The integer cutoff is floor(C ell) inside the proof; s is never rounded. A fixed exponential margin absorbs the prefactor and cutoff loss. Local and event comparisons retain the identical S, direction and actual history law."))), DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula N(byte n) => D(n);
    private static Formula Call(string name, params Formula[] args)
    {
        var p = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) p.AddRange([Comma, Sp]); p.Add(args[i]); }
        p.Add(Close); return Seq([.. p]);
    }
    private static Formula Q(string names, Formula type, Formula body) => Seq(Forall, Sp,
        Seq([.. names.Split(' ').SelectMany((s, i) => i == 0 ? new[] { V(s) } : new[] { Comma, V(s) })]), Colon, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) => Seq(Exists, Sp, V(name), Colon, type, Comma, Sp, body);
    private static Formula EqF(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula LtF(Formula a, Formula b) => Seq(a, Lt, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Leq, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Plus, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Close, Sp, Cdot, Sp, Open, b, Close);
    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Pow(Formula a, Formula b) => Seq(Grp(a), Caret, Grp(b));
    private static Formula AbsF(Formula a) => Seq(Lvert, Sp, a, Sp, Rvert);
    private static Formula Fn(Formula a, Formula b) => Seq(a, To, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Sp, Rightarrow, Sp, b);
    private static Formula And(params Formula[] xs)
    {
        var p = new List<Formula>();
        for (var i = 0; i < xs.Length; i++) { if (i > 0) p.AddRange([Sp, Land, Sp]); p.Add(xs[i]); }
        return Seq([.. p]);
    }
    private static Formula M => Pow(N(2), V("d"));
    private static Formula Ell => Call("ell", V("d"));
    private static Formula Counts => Call("CountTuples", V("k"));
    private static Formula Nu(Formula e) => Call("poissonEvent", V("r"), V("S"), V("reverse"), V("m"), Call("s", V("d")), e);
    private static Formula Actual(Formula e) => Call("sourceEvent", V("r"), V("S"), V("reverse"), V("m"), Call("s", V("d")), V("e"), e);
    private static Formula Relative => Div(Mul(V("A"), Pow(Ell, Add(V("k"), N(1)))), Mul(N(2), M));
    private static Formula Reg => Call("SourceRegime", V("r"), V("beta"), V("alpha"), V("q"), V("s"));
    private static Formula Eventually(Formula body) => Ex("dimensionThreshold", V("Nat"),
        Q("d", V("Nat"), Imp(Le(V("dimensionThreshold"), V("d")), body)));
    private static Formula Objects(Formula body) => Q("k", V("Nat"), Imp(Call("oneOrTwo", V("k")),
        Q("S", Call("CubeSupport", V("d"), Call("q", V("d"))),
        Q("m", Call("PositiveMarks", V("d"), V("k")), Imp(Call("injective", V("m")),
        Q("reverse", V("Bool"), Q("e", Call("Experiment"), body)))))));
    private static Formula Regime() => EqF(Reg, And(LtF(N(0), V("r")), LtF(V("r"), N(1)),
        LtF(Div(N(1), N(2)), V("beta")), LtF(V("beta"), N(1)), LtF(N(0), V("alpha")),
        Ex("delta", Call("RealSequence"), And(Call("tendsToZero", V("delta")), Eventually(EqF(Call("q", V("d")),
            Pow(M, Add(Sub(N(1), V("beta")), Call("delta", V("d")))))))),
        Call("tendsTo", Call("timeToLogRatioSequence", V("s")), V("alpha"))));
    private static Formula PointScale => Div(V("s"), Mul(N(2), M));
    private static Formula CountData(Formula body) => Q("d q s k", V("Nat"), Q("r", V("Real"),
        Q("S", Call("CubeSupport", V("d"), V("q")), Q("reverse", V("Bool"),
        Q("m", Call("PositiveMarks", V("d"), V("k")), body)))));
    private static Formula Rates() => EqF(Call("sourceRates", V("r"), V("S"), V("reverse"), V("m"), V("s")),
        Call("nonnegativeParityRates", Div(Mul(PointScale, Add(N(1), Call("directionalProfile", V("reverse"), V("r"), V("S"), V("m")))), N(2)),
            Div(Mul(PointScale, Sub(N(1), Call("directionalProfile", V("reverse"), V("r"), V("S"), V("m")))), N(2))));
    private static Formula ExactMeans() => Q("j", Call("Fin", V("k")), Q("sigma", Call("Signs"), And(
        EqF(Call("actualOneEdgeProbability", V("r"), V("S"), V("reverse"), V("m"), V("j"), V("sigma")),
            Div(Add(N(1), Mul(V("sigma"), Call("directionalProfile", V("reverse"), V("r"), V("S"), V("m"), V("j")))), Mul(N(2), Mul(N(2), M)))),
        EqF(Call("sourceRate", V("r"), V("S"), V("reverse"), V("m"), V("s"), V("j"), V("sigma")),
            Mul(V("s"), Call("actualOneEdgeProbability", V("r"), V("S"), V("reverse"), V("m"), V("j"), V("sigma")))))));
    private static Formula Local()
    {
        Formula point = Call("singleton", V("n"));
        Formula mass = And(LtF(N(0), Nu(point)), Le(AbsF(Sub(Div(Actual(point), Nu(point)), N(1))), Relative));
        Formula local = Q("n", Counts, Imp(Le(Call("total", V("n")), Mul(V("C"), Ell)), mass));
        Formula body = Objects(And(Call("ExactDirectionalMeans", V("r"), V("S"), V("reverse"), V("m"), Call("s", V("d"))), local));
        Formula sequences = Q("beta", V("Real"), Q("q s", Fn(V("Nat"), V("Nat")), Imp(Reg, Eventually(body))));
        Formula hypotheses = And(LtF(N(0), V("r")), LtF(V("r"), N(1)), LtF(N(0), V("alpha")), LtF(N(0), V("C")));
        return Q("r alpha C", V("Real"), Imp(hypotheses, Ex("A", V("Real"), And(LtF(N(0), V("A")), sequences))));
    }
    private static Formula TailEvents()
    {
        Formula tail = Call("totalExceeds", Mul(V("C"), Ell));
        Formula remainder = Pow(M, Sub(N(0), V("D")));
        Formula tailBound = Le(Add(Actual(tail), Nu(tail)), remainder);
        Formula events = Q("E", Call("Set", Counts), Le(AbsF(Sub(Actual(V("E")), Nu(V("E")))), Add(Mul(Relative, Nu(V("E"))), remainder)));
        Formula body = Objects(And(tailBound, events));
        Formula sequences = Q("beta", V("Real"), Q("q s", Fn(V("Nat"), V("Nat")), Imp(Reg, Eventually(body))));
        Formula hypotheses = And(LtF(N(0), V("r")), LtF(V("r"), N(1)), LtF(N(0), V("alpha")), LtF(N(0), V("D")));
        return Q("r alpha D", V("Real"), Imp(hypotheses, Ex("C", V("Real"), Ex("A", V("Real"),
            And(LtF(N(0), V("C")), LtF(N(0), V("A")), sequences)))));
    }
    private static Formula HCV(string s) => F.Id(s);
    private static Formula HCN(byte n) => D(n);
    private static Formula HCCall(string name, params Formula[] args)
    {
        var p = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) p.AddRange([Comma, Sp]); p.Add(args[i]); }
        p.Add(Close); return Seq([.. p]);
    }
    private static Formula HCQ(string names, Formula type, Formula body) =>
        Seq(Forall, Sp, Seq([.. names.Split(' ').SelectMany((s, i) => i == 0 ? new[] { HCV(s) } : new[] { Comma, HCV(s) })]), Colon, type, Comma, Sp, body);
    private static Formula HCFn(Formula a, Formula b) => Seq(a, To, Sp, b);
    private static Formula HCEqn(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula HCAdd(Formula a, Formula b) => Seq(a, Plus, b);
    private static Formula HCPow(Formula a, Formula b) => Seq(Grp(a), Caret, Grp(b));
    private static Formula HCAndF(params Formula[] xs) => HCJoin(xs, Land);
    private static Formula HCJoin(Formula[] xs, Formula op)
    {
        var p = new List<Formula>();
        for (var i = 0; i < xs.Length; i++) { if (i > 0) p.AddRange([Sp, op, Sp]); p.Add(xs[i]); }
        return Seq([.. p]);
    }
    private static Formula HCFinF(Formula a) => HCCall("Fin", a);
    private static Formula HCCubeData(Formula body) => HCQ("d q", HCV("Nat"), HCQ("r", HCV("Real"), HCQ("S", HCCall("CubeSupport", HCV("d"), HCV("q")), body)));
    private static Formula HCCubeHistoryData(Formula body) => HCQ("d q s", HCV("Nat"), HCQ("r", HCV("Real"), HCQ("S", HCCall("CubeSupport", HCV("d"), HCV("q")), HCQ("reverse", HCCall("Bool"), HCQ("e", HCCall("Experiment"), body)))));
    private static Formula HCTransport()
    {
        Formula v(Formula x) => HCCall("cubeEquiv", HCV("d"), x);
        Formula ns = HCCall("cubeSupportEquiv", HCV("d"), HCV("q"), HCV("S"));
        Formula history = HCCall("historyEquiv", HCV("d"), HCV("s"), HCV("e"));
        Formula ho = HCCall("apply", history, HCV("o"));
        Formula cube = HCCall("Cube", HCV("d"));
        Formula carrier = HCCall("CubeObs", HCV("d"), HCV("s"), HCV("e"));
        Formula nativeCarrier = HCCall("Obs", HCPow(HCN(2), HCV("d")), HCV("s"), HCV("e"));
        Formula parities = HCQ("x", cube, HCEqn(HCCall("chi", v(HCV("x"))), HCCall("parity", HCV("x"))));
        Formula kernels = HCEqn(HCCall("cubeKernel", HCV("r"), HCV("S"), HCV("reverse"), HCV("x"), HCV("y")), HCCall("nativeKernel", HCV("r"), ns, HCV("reverse"), v(HCV("x")), v(HCV("y"))));
        Formula masses = HCEqn(HCCall("cubeProbability", HCV("r"), HCV("S"), HCV("reverse"), HCV("e"), HCV("o")), HCCall("nativeMass", HCV("r"), ns, HCV("reverse"), HCV("e"), ho));
        Formula originalRow = HCCall("inverse", HCCall("cubeEquiv", HCV("d")), HCCall("inl", HCV("i")));
        Formula counts = HCEqn(HCCall("cubeCount", HCV("e"), HCV("o"), originalRow, HCV("sigma")), HCCall("count", HCV("e"), ho, HCV("i"), HCV("sigma")));
        Formula events = HCEqn(HCCall("cubeEventMass", HCV("d"), HCV("r"), HCV("S"), HCV("reverse"), HCV("e"), history, HCV("E")), HCCall("nativeEventMass", HCV("r"), ns, HCV("reverse"), HCV("e"), HCV("E")));
        Formula countClause = HCQ("o", carrier, HCQ("i", HCFinF(HCPow(HCN(2), HCV("d"))), HCQ("sigma", HCV("Real"), counts)));
        return HCCubeHistoryData(HCAndF(parities, HCQ("x y", cube, kernels), HCQ("o", carrier, masses),
            countClause, HCQ("E", HCFn(nativeCarrier, HCV("Prop")), events)));
    }


}

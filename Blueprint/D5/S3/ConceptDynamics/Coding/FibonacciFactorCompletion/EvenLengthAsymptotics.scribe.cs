using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class EvenLengthAsymptoticsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EvenLengthAsymptotics.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.ForAll, [..v], p);
    private static Formula Ex(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.Exists, [..v], p);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(params Formula[] p)
    {
        var r = p[^1];
        for (var k = p.Length - 2; k >= 0; --k) r = new Formula.Logic(p[k], FormulaLogicOperator.And, r);
        return r;
    }
    private static Formula Nat => I("Nat");
    private static Formula Real => I("Real");
    private static Formula Model => I("Model");
    private static Formula Bool => I("Bool");
    private static Formula Side => I("Side");
    private static Formula Contract => I("Contract");
    private static Formula Returns => Call("List", I("Return"));
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Lam(string n, Formula t, Formula p) => Seq(Open, I(n), Sp, Colon, Sp, t, Sp, Mapsto, Sp, p, Close);
    private static Formula Add(Formula a, Formula b) => Call("add", a, b);
    private static Formula Sub(Formula a, Formula b) => Call("subtract", a, b);
    private static Formula Mul(Formula a, Formula b) => Call("multiply", a, b);
    private static Formula Div(Formula a, Formula b) => Call("divide", a, b);
    private static Formula Pow(Formula a, Formula b) => Call("power", a, b);
    private static Formula Lt(Formula a, Formula b) => Call("lt", a, b);
    private static Formula Le(Formula a, Formula b) => Call("le", a, b);
    private static Formula Ap(Formula a, Formula b) => Call("apply", a, b);
    private static Formula Cast(Formula a) => Call("toReal", a);
    private static Formula Even(Formula a) => Call("Even", a);
    private static Formula W(Formula xs) => Call("listWeight", xs);
    private static Formula J(Formula f) => Call("fillerJ", f);
    private static Formula Q(Formula f) => Call("fillerQ", f);
    private static Formula Filler(Formula f) => Call("lowFiller", f);
    private static Formula Copies(Formula l, Formula t) => Call("paddingCopies", l, t);
    private static Formula Remainder(Formula l, Formula t) => Call("paddingWeight", l, t);
    private static Formula Low(Formula q) => Call("lowReturn", q);
    private static Formula Start(Formula m) => Call("initial", I("high"), m);
    private static Formula Trace(Formula d, Formula strict, Formula xs, Formula state) =>
        Call("GuardTrace", I("K"), d, strict, I("high"), xs, state);
    private static Formula Supply(Formula m, Formula budget, Formula contract, Formula xs) =>
        Call("ActualPairSupply", m, I("o"), budget, contract, xs);
    private static Formula Count(Formula m, Formula strict, Formula t) =>
        Call("actualCount", m, I("K"), Threshold, strict, t);
    private static Formula ContractCount(Formula m, Formula contract, Formula t) =>
        Call("contractCount", m, I("o"), I("b"), contract, t);
    private static Formula LogRate(Formula m, Formula strict, Formula t) =>
        Call("actualLogRate", m, I("K"), Threshold, strict, t);
    private static Formula Log(Formula a) => Call("logb", D(2), Cast(a));
    private static Formula H => Call("hSide", I("high"));
    private static Formula A => Call("aSide", I("high"));
    private static Formula Scale => Mul(Pow(I("g"), D(2)), Pow(I("chi"), I("K")));
    private static Formula ThresholdValue => Div(Div(Sub(I("lam"), I("b")), Pow(I("g"), D(2))), Pow(I("chi"), I("K")));
    private static Formula Threshold => Call("d",I("b"),I("K"));
    private static Formula Floor => Sub(H, Mul(Pow(I("rho"), Call("m", I("R"))), Sub(H, Mul(I("chi"), A))));
    private static Formula DeltaValue => Sub(Floor, Start(I("sourceModel")));
    private static Formula Delta => Call("delta",I("R"),I("sourceModel"));
    private static Formula GammaValue => Mul(Delta, Pow(I("g"), I("N")));
    private static Formula Gamma => Call("gamma",I("R"),I("sourceModel"),I("N"));
    private static Formula EpsilonValue => Div(Call("min", Sub(I("b"), Call("actualAutomaticCost", I("K"))), Mul(Scale, Gamma)), D(2));
    private static Formula Epsilon => Call("epsilon",I("R"),I("sourceModel"),I("b"),I("K"),I("N"));
    private static Formula LValue => Add(Add(I("N"), D(2, 0)), Mul(D(6), Call("m", I("R"))));
    private static Formula L => Call("blockWeight",I("R"),I("N"));
    private static Formula KCopies => Copies(L, I("T"));
    private static Formula FillWeight => Remainder(L, I("T"));
    private static Formula ACount => Count(I("sourceModel"), I("false"), I("N"));
    private static Formula PowerCount => Pow(ACount, KCopies);
    private static Formula BookValue => Call("Subtype", Lam("xs", Returns,
        And(Trace(Threshold, I("false"), I("xs"), Start(I("sourceModel"))), Equal(W(I("xs")), I("N")))));
    private static Formula Book => Call("weakBook",I("sourceModel"),I("b"),I("K"),I("N"));
    private static Formula Choices => Fn(Call("Fin", KCopies), Book);
    private static Formula ChoiceWords => Call("ofFn", Lam("i", Call("Fin", KCopies), Call("val", Ap(I("z"), I("i")))));
    private static Formula Unpadded => Call("resetConcatenation", I("R"), ChoiceWords);
    private static Formula Execution => Call("paddedExecution", I("R"), ChoiceWords, FillWeight);
    private static Formula Budget => And(Le(D(2), I("K")), Lt(Sub(I("lam"), Mul(Scale, H)), I("b")),
        Lt(I("b"), Sub(I("lam"), Mul(Scale, Div(A, Sub(D(1), Mul(I("rho"), Pow(I("chi"), I("K")))))))));
    private static Formula Parameters(Formula p) => All(Imp(Budget, p),
        B("o", I("Ownership")), B("b", Real), B("K", Nat));
    private static Formula Reset(Formula p) => Ex(And(Equal(Call("r", I("R")), D(1)),
        Lt(Call("max", Call("max", Call("xSide", I("high")), Call("ySide", I("high"))), Threshold), Floor),
        All(Imp(And(Lt(D(0), I("N")), Le(D(1), ACount)), p), B("sourceModel", Model), B("N", Nat))), B("R", I("Return")));
    private static Formula Target(Formula p) => All(Imp(And(Le(D(7, 8), I("T")), Even(I("T"))), p), B("targetModel", Model), B("T", Nat));
    private static Formula CountBounds => And(All(Le(PowerCount, Count(I("targetModel"), I("strict"), I("T"))), B("strict", Bool)),
        All(Le(PowerCount, ContractCount(I("targetModel"), I("contract"), I("T"))), B("contract", Contract)));
    private static Formula Half(Formula f) => Div(f, D(2));
    private static Formula Mod3(Formula n) => Call("mod", n, D(3));
    private static Formula FillerStatement()
    {
        var f = I("F"); var j = J(f); var q = Q(f); var half = Half(f);
        return All(Imp(And(Even(f), Le(D(7, 8), f)), And(Le(D(1), j), Le(j, D(3)),
            All(Imp(And(Le(D(1), I("i")), Le(I("i"), D(3)), Equal(Mod3(half), Mod3(I("i")))), Equal(I("i"), j)), B("i", Nat)),
            Equal(Mod3(half), Mod3(j)), Le(Mul(D(1, 3), j), half), Call("dvd", D(3), Sub(half, Mul(D(1, 3), j))),
            Equal(Add(Mul(D(2, 6), j), Mul(D(6), q)), f), Equal(W(Filler(f)), f),
            All(Imp(Call("member", I("a"), Filler(f)), Equal(Call("r", I("a")), D(1))), B("a", I("Return"))),
            All(Imp(Le(D(2), I("K")), All(Call("GuardTrace", I("K"), I("d"), I("strict"), I("side"), Filler(f), I("D")),
                B("d", Real), B("strict", Bool), B("side", Side), B("D", Real))), B("K", Nat)))), B("F", Nat));
    }
    private static Formula PaddingFacts(Formula l, Formula t) => And(Even(Remainder(l, t)), Le(D(7, 8), Remainder(l, t)),
        Lt(Remainder(l, t), Add(D(7, 8), l)), Equal(Add(Mul(Copies(l, t), l), Remainder(l, t)), t));
    private static Formula PrefixFacts => All(Imp(And(Equal(Execution, Call("append", I("before"), Call("cons", I("a"), I("after")))),
        Equal(Call("r", I("a")), I("K"))), Ex(Equal(Unpadded, Call("append", I("before"), Call("cons", I("a"), I("rest")))), B("rest", Returns))),
        B("before", Returns), B("a", I("Return")), B("after", Returns));
    private static Formula ReverseFacts => All(Equal(Call("externalWord", I("side"), Execution),
        Call("append", Call("externalWord", I("side"), Filler(FillWeight)), Call("externalWord", I("side"), Unpadded))), B("side", Side));
    private static Formula FiniteStatement() => Parameters(Reset(And(Even(I("N")), Even(L), Lt(D(0), L), Lt(D(0), Delta), Lt(D(0), Gamma), Lt(D(0), Epsilon),
        Target(And(PaddingFacts(L, I("T")), Call("Injective", Lam("z", Choices, Execution)),
            All(And(Equal(W(Execution), I("T")), Trace(Add(Threshold, Gamma), I("false"), Execution, Start(I("targetModel"))),
                Supply(I("targetModel"), Sub(I("b"), Epsilon), I("strict"), Execution),
                All(Supply(I("targetModel"), I("b"), I("contract"), Execution), B("contract", Contract)), PrefixFacts, ReverseFacts), B("z", Choices)),
            CountBounds, Call("Injective", Lam("z", Choices, Call("history", I("targetModel"), Execution))),
            All(Call("Injective", Lam("z", Choices, Call("source", I("side"), I("targetModel"), Execution))), B("side", Side)))))));
    private static Formula OddCounts(bool arbitrary)
    {
        var actual = arbitrary
            ? Call("actualCount", I("model"), I("K"), I("d"), I("strict"), I("T"))
            : Count(I("model"), I("strict"), I("T"));
        var contracts = ContractCount(I("model"), I("contract"), I("T"));
        return And(arbitrary
                ? All(Equal(actual, D(0)), B("model", Model), B("K", Nat), B("d", Real), B("strict", Bool))
                : All(Equal(actual, D(0)), B("model", Model), B("strict", Bool)),
            arbitrary
                ? All(Equal(contracts, D(0)), B("model", Model), B("o", I("Ownership")), B("b", Real), B("contract", Contract))
                : All(Equal(contracts, D(0)), B("model", Model), B("contract", Contract)));
    }
    private static Formula PositiveCounts => And(Equal(W(Filler(I("T"))), I("T")),
        All(And(Supply(I("model"), I("b"), I("contract"), Filler(I("T"))),
            Lt(D(0), ContractCount(I("model"), I("contract"), I("T")))), B("model", Model), B("contract", Contract)),
        All(And(Lt(D(0), Count(I("model"), I("strict"), I("T"))), Equal(LogRate(I("model"), I("strict"), I("T")),
            Div(Log(Count(I("model"), I("strict"), I("T"))), Cast(I("T"))))), B("model", Model), B("strict", Bool)));
    private static Formula OriginalStatement() => Parameters(And(All(Imp(Call("Odd", I("T")), OddCounts(false)), B("T", Nat)),
        All(Imp(And(Even(I("T")), Le(D(7, 8), I("T"))), PositiveCounts), B("T", Nat)),
        Reset(And(Even(I("N")), Even(L), Lt(D(0), L), Target(CountBounds),
            All(Le(Div(Log(ACount), Cast(L)), Call("liminf", Lam("v", Nat,
                LogRate(I("targetModel"), I("strict"), Mul(D(2), I("v")))), I("atTop"))), B("targetModel", Model), B("strict", Bool))))));
    private static Formula Offset(Formula m) => Call("observationOffset", m);
    private static Formula Nobs(Formula m, Formula t) => Add(Offset(m), t);
    private static Formula Hist(Formula m, Formula xs) => Call("history", m, xs);
    private static Formula Length(Formula x) => Call("length", x);
    private static Formula Src(Formula side, Formula m, Formula xs) => Call("source", side, m, xs);
    private static Formula Observed(Formula m, Formula c, Formula n) =>
        Call("ObservedContractDictionary", m, I("o"), I("b"), c, n);
    private static Formula HistImage(Formula m, Formula c, Formula n) =>
        Call("ActualHistoryImage", m, I("o"), I("b"), c, n);
    private static Formula SrcImage(Formula side, Formula m, Formula c, Formula n) =>
        Call("ActualSourceImage", side, m, I("o"), I("b"), c, n);
    private static Formula PairImage(Formula m, Formula c, Formula n) =>
        Call("ActualSourcePairImage", m, I("o"), I("b"), c, n);
    private static Formula HistCount(Formula m, Formula c, Formula n) =>
        Call("historyImageCount", m, I("o"), I("b"), c, n);
    private static Formula SrcCount(Formula side, Formula m, Formula c, Formula n) =>
        Call("sourceImageCount", side, m, I("o"), I("b"), c, n);
    private static Formula PairCount(Formula m, Formula c, Formula n) =>
        Call("sourcePairImageCount", m, I("o"), I("b"), c, n);
    private static Formula EvenIndex => Mul(D(2), I("v"));
    private static Formula Eta => Call("etaB", I("K"), I("b"));
    private static Formula RawLimit(Formula count) => Call("Tendsto",
        Lam("v", Nat, Div(Log(count), Cast(EvenIndex))), I("atTop"), Call("nhds", Eta));
    private static Formula RawError(Formula count) => Call("IsLittleO", I("atTop"),
        Lam("v", Nat, Sub(Log(count), Mul(Eta, Cast(EvenIndex)))),
        Lam("v", Nat, Cast(EvenIndex)));
    private static Formula RawAsymptotics(Formula count) => And(RawLimit(count), RawError(count));
    private static Formula ObservationCounts(Formula m, Formula c, Formula t) => And(
        Equal(HistCount(m, c, Nobs(m, t)), ContractCount(m, c, t)),
        All(Equal(SrcCount(I("side"), m, c, Nobs(m, t)), ContractCount(m, c, t)), B("side", Side)),
        Equal(PairCount(m, c, Nobs(m, t)), ContractCount(m, c, t)));
    private static Formula OriginalParameterSet(Formula p) => All(p,
        B("model", Model), B("o", I("Ownership")), B("b", Real), B("contract", Contract), B("Nobs", Nat));
    private static Formula ObservedDefinition() => OriginalParameterSet(Equal(
        Observed(I("model"), I("contract"), I("Nobs")),
        Call("Subtype", Lam("xs", Returns, And(Supply(I("model"), I("b"), I("contract"), I("xs")),
            Equal(Length(Hist(I("model"), I("xs"))), I("Nobs")))))));
    private static Formula ImageDefinition(string kind)
    {
        var m = I("model"); var c = I("contract"); var n = I("Nobs");
        var xs = Call("val", I("xs"));
        var value = kind == "history" ? Hist(m, xs) : kind == "source"
            ? Src(I("side"), m, xs) : Call("pair", Src(I("high"), m, xs), Src(I("low"), m, xs));
        var image = kind == "history" ? HistImage(m, c, n) : kind == "source"
            ? SrcImage(I("side"), m, c, n) : PairImage(m, c, n);
        var equality = Equal(image, Call("range", Lam("xs", Observed(m, c, n), value)));
        return OriginalParameterSet(kind == "source" ? All(equality, B("side", Side)) : equality);
    }
    private static Formula ImageCountDefinition(string kind)
    {
        var m = I("model"); var c = I("contract"); var n = I("Nobs");
        var image = kind == "history" ? HistImage(m, c, n) : kind == "source"
            ? SrcImage(I("side"), m, c, n) : PairImage(m, c, n);
        var count = kind == "history" ? HistCount(m, c, n) : kind == "source"
            ? SrcCount(I("side"), m, c, n) : PairCount(m, c, n);
        var equality = Equal(count, Call("card", image));
        return OriginalParameterSet(kind == "source" ? All(equality, B("side", Side)) : equality);
    }
    private static Formula ObservationSupplier(Formula m, Formula c, Formula t)
    {
        var xs = Call("val", I("xs")); var side = I("side"); var n = Nobs(m, t);
        var prefix = Call("observedPrefix", side, m, xs);
        var sourcePrefix = Call("sourcePrefix", side, m, xs);
        var err = Ap(I("err"), I("p"));
        var observed = Call("observe", I("o"), Call("coordinate", sourcePrefix, I("p")), err);
        var futurePosition = Add(n, I("p"));
        var future = Call("observe", I("o"), Call("coordinate", sourcePrefix, futurePosition), Ap(I("err"), futurePosition));
        return All(And(Equal(W(xs), t), All(And(Equal(Length(prefix), n),
            Call("OperationRecord", I("o"), I("b"), c, Src(side, m, xs), Call("OperationPairedRecord", m, I("o"), xs, side)),
            Call("OperationFiniteSource", Src(side, m, xs)),
            All(Equal(Ap(Src(side, m, xs), futurePosition), Call("address", Call("tailPrefix", side), I("p"))), B("p", Nat)),
            Ex(And(Call("ErrorBound", I("b"), c, I("err")),
                All(Imp(Lt(I("p"), n), Equal(observed, Call("getElem", Hist(m, xs), I("p")))), B("p", Nat)),
                All(Imp(Le(n, I("p")), Equal(err, D(0))), B("p", Nat)),
                All(Equal(future, Call("observe", I("o"), Call("coordinate", Call("tailPrefix", side), I("p")), D(0))), B("p", Nat))),
                B("err", Fn(Nat, Real)))), B("side", Side))), B("xs", Observed(m, c, n)));
    }
    private static Formula CorrespondenceStatement()
    {
        var m = I("model"); var c = I("contract"); var t = I("T");
        return Parameters(All(And(Call("Finite", Observed(m, c, Nobs(m, t))),
            ObservationCounts(m, c, t), Equal(ContractCount(m, c, t),
                Count(m, Call("contractStrict", I("o"), c), t)), ObservationSupplier(m, c, t)),
            B("model", Model), B("contract", Contract), B("T", Nat)));
    }
    private static Formula ReindexStatement()
    {
        var offset = Offset(I("model")); var v = I("v");
        var back = Sub(v, Div(offset, D(2)));
        return All(And(Even(offset),
            Call("Tendsto", Lam("v", Nat, Add(offset, EvenIndex)), I("atTop"), I("atTop")),
            Call("Tendsto", Lam("v", Nat, back), I("atTop"), I("atTop")),
            Call("Eventually", Lam("v", Nat, Equal(Add(offset, Mul(D(2), back)), EvenIndex)), I("atTop"))), B("model", Model));
    }
    private static Formula ObservationAsymptoticsStatement()
    {
        var m = I("model"); var c = I("contract"); var t = I("T"); var n = I("Nobs");
        return Parameters(All(And(
            All(Imp(Call("Odd", n), And(Equal(HistCount(m, c, n), D(0)),
                All(Equal(SrcCount(I("side"), m, c, n), D(0)), B("side", Side)),
                Equal(PairCount(m, c, n), D(0)))), B("Nobs", Nat)),
            All(ObservationCounts(m, c, t), B("T", Nat)),
            All(Imp(And(Even(t), Le(D(7, 8), t)), And(Lt(D(0), HistCount(m, c, Nobs(m, t))),
                All(Lt(D(0), SrcCount(I("side"), m, c, Nobs(m, t))), B("side", Side)),
                Lt(D(0), PairCount(m, c, Nobs(m, t))))), B("T", Nat)),
            RawAsymptotics(HistCount(m, c, EvenIndex)),
            All(RawAsymptotics(SrcCount(I("side"), m, c, EvenIndex)), B("side", Side)),
            RawAsymptotics(PairCount(m, c, EvenIndex))), B("model", Model), B("contract", Contract)));
    }
    private static DocumentBlock Notation() => new DocumentBlock.Section(H("Shared notation"),Blocks(
        Paragraph(Text("The following functions abbreviate exactly the displayed expressions. Every occurrence uses the arguments shown, within the scope of the same quantified parameters and witnesses. Expanding these definitions recovers all guards, weights and shared margins.")),
        Paragraph(Math(Disp(All(Equal(Threshold,ThresholdValue),B("b",Real),B("K",Nat))))),
        Paragraph(Math(Disp(All(Equal(Delta,DeltaValue),B("R",I("Return")),B("sourceModel",I("Model")))))),
        Paragraph(Math(Disp(All(Equal(Gamma,GammaValue),B("R",I("Return")),B("sourceModel",I("Model")),B("N",Nat))))),
        Paragraph(Math(Disp(All(Equal(Epsilon,EpsilonValue),B("R",I("Return")),B("sourceModel",I("Model")),B("b",Real),B("K",Nat),B("N",Nat))))),
        Paragraph(Math(Disp(All(Equal(L,LValue),B("R",I("Return")),B("N",Nat))))),
        Paragraph(Math(Disp(All(Equal(Book,BookValue),B("sourceModel",I("Model")),B("b",Real),B("K",Nat),B("N",Nat)))))));
    private static DocumentBlock Node(string name, Formula formula, string prose, bool definition = false) => Describe.Lean(
        DescribeId.Create("fib-even-length-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(name.Replace('_', ' ')), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The raw logarithms of actual strict and weak complete-list counts equal eta_b times the literal weight plus a little-o error on all even weights. Actual histories and both literal sources retain the same coefficient at the original observation offsets twenty-six and fifty-two.",
        H("Actual complete counts on all even lengths"), Blocks(
        Notation(),
        Paragraph(Text("Return lists are in execution order from the literal tail outward. Their literal weights are six times m plus twenty times r. The two models start at X_H and Y_H on the high side and at the corresponding X_L and Y_L on the low side. All source supplies use the original U/V and C blocks, the same stems and paid anchors, and the original literal tails. The external source reverses the return list without reversing the labels inside any block. Natural-number division and subtraction below use the natural quotient and truncated subtraction.")),
        Paragraph(Text("The weak complete-list count uses the non-strict high guard. It corresponds to the closed source contract when the nearest high endpoint is owned, o(0)=true; otherwise the closed contract uses the strict high guard. The strict and recordMargin source contracts always use the strict high guard.")),
        Node("fillerJ", All(Equal(J(I("F")), Call("ifThenElse", Equal(Mod3(Half(I("F"))), D(0)), D(3), Mod3(Half(I("F"))))), B("F", Nat)),
            "The residue zero is represented by three; the other two residues are represented by one and two.", true),
        Node("fillerQ", All(Equal(Q(I("F")), Div(Sub(Half(I("F")), Mul(D(1, 3), J(I("F")))), D(3))), B("F", Nat)),
            "For even F at least seventy-eight, the numerator is nonnegative and divisible by three.", true),
        Node("lowReturn", All(And(Equal(Call("m", Low(I("q"))), Add(D(1), I("q"))), Equal(Call("r", Low(I("q"))), D(1))), B("q", Nat)),
            "This is the positive return (1+q,1), of literal weight twenty-six plus six times q.", true),
        Node("lowFiller", All(Equal(Filler(I("F")), Call("cons", Low(Q(I("F"))), Call("replicate", Sub(J(I("F")), D(1)), Low(D(0))))), B("F", Nat)),
            "The first return carries all additional six-letter blocks. The remaining j-1 returns are (1,1). This one filler depends only on F.", true),
        Node("actual_list_weight_even", All(Even(W(I("xs"))), B("xs", Returns)),
            "Every summand six times m plus twenty times r is even. The empty list has weight zero."),
        Node("low_filler_geometry", FillerStatement(),
            "For F=2v at least seventy-eight, v is at least thirty-nine. The unique representative j lies between one and three, so 13j is at most v. Dividing v-13j by three gives q and the exact weight 26j+6q=F. Every return has r=1<K, hence its guard passes for either strictness flag, either side and every input displacement. The three smallest residues are F=78 with (j,q)=(3,0), F=80 with (1,9), and F=82 with (2,5)."),
        Node("paddingCopies", All(Equal(Copies(I("L"), I("T")), Div(Sub(I("T"), D(7, 8)), I("L"))), B("L", Nat), B("T", Nat)),
            "The number of complete reset codewords is the quotient of T-78 by L.", true),
        Node("paddingWeight", All(Equal(Remainder(I("L"), I("T")), Sub(I("T"), Mul(Copies(I("L"), I("T")), I("L")))), B("L", Nat), B("T", Nat)),
            "The remainder includes the reserved seventy-eight units for the outer filler.", true),
        Node("even_padding_arithmetic", All(Imp(And(Lt(D(0), I("L")), Even(I("L")), Le(D(7, 8), I("T")), Even(I("T"))), PaddingFacts(I("L"), I("T"))), B("L", Nat), B("T", Nat)),
            "The exact decomposition is T=kL+F with even F in [78,78+L). At T=78, k is zero. At T=78+L, k is one and F returns to seventy-eight."),
        Node("paddedExecution", All(Equal(Call("paddedExecution", I("R"), I("words"), I("F")),
            Call("append", Call("resetConcatenation", I("R"), I("words")), Filler(I("F")))), B("R", I("Return")), B("words", Call("List", Returns)), B("F", Nat)),
            "The filler follows all codewords in execution order. It therefore precedes the original codeword list in the external source, on its outer side.", true),
        Node("same_reset_all_even_counts", FiniteStatement(),
            "The budget inequalities fix d=(lambda-b)/(g squared times chi to K). One low reset R is fixed before all source models and all N. Its floor B exceeds X_H, Y_H and d. For the full nonempty weak exact-N codebook, delta=B-D0, gamma=delta times g to N, and epsilon is half the minimum of b-C_auto and g squared times chi to K times gamma. Nonemptiness gives even N from an actual list, so L=N+20+6m(R) is positive and even. Append the same filler to every k-tuple. Every old high return has exactly its old execution prefix, while all filler returns are low. The original actual supply at b-epsilon extends to the same literal sources and zero-error futures. Cancelling the common filler and applying the reset parser with positive cumulative-weight cuts recovers all choices even when codeword letter lengths differ. The resulting exact-T actual dictionaries, every source contract, the color histories and both literal source sides all preserve those distinct choices."),
        Node("odd_actual_counts", All(Imp(Call("Odd", I("T")), OddCounts(true)), B("T", Nat)),
            "No list of positive actual returns can have odd literal weight. Every strict, weak and source-contract dictionary at an odd weight is empty."),
        Node("even_actual_positivity", Parameters(All(Imp(And(Even(I("T")), Le(D(7, 8), I("T"))), PositiveCounts), B("T", Nat))),
            "The standalone low filler is strictly feasible from both models and supplies all original contracts. Every raw even count is positive at T at least seventy-eight. On this range, positivity permits max-one normalization to be removed from the logarithm."),
        Node("full_even_floor_ratio", All(Imp(And(Lt(D(0), I("L")), Even(I("L"))), Call("Tendsto", Lam("v", Nat,
            Div(Cast(Copies(I("L"), Mul(D(2), I("v")))), Cast(Mul(D(2), I("v"))))), I("atTop"), Call("nhds", Div(D(1), Cast(I("L")))))), B("L", Nat)),
            "The bounded filler weight divided by T tends to zero on all T=2v. The exact decomposition kL+F=T gives k/T tending to 1/L on this full even filter."),
        Node("original_finite_even_bridge", OriginalStatement(),
            "Odd counts vanish, and all even raw counts are positive from weight seventy-eight onward. The same reset works for every fixed nonempty full weak codebook, for both target starts and both guard flags. Its exact-T power counts imply the normalized full-even liminf is at least log base two of a_N divided by N+C_R. The fixed-codebook bound holds on the entire even-weight filter. Positive-count codebook slopes approaching eta_b therefore bound this same liminf from below."),
        Node("actual_even_raw_asymptotics", Parameters(All(RawAsymptotics(Count(I("model"), I("strict"), EvenIndex)), B("model", Model), B("strict", Bool))),
            "Fix one reset of the all-even construction before choosing any source weight or target model. An unbounded positive-count sequence of original weak actual dictionaries has raw slope log2(a_N)/N tending to eta_b. For this exact fixed reset, N/(N+C_R) tends to one, so its codebook slopes also tend to eta_b. The full-even liminf is at least every one of these slopes for both target models and both guard flags. Boundedness of the original normalized sequence gives a full-even limsup at most its unrestricted limsup eta_b. The two bounds give the limit. The actual low filler makes every raw count positive at even T at least seventy-eight; only there is max-one normalization removed. Subtracting eta_b from the raw quotient gives zero limit, exactly the stated little-o error."),
        Node("ObservedContractDictionary", ObservedDefinition(),
            "The indexing length is the length of the original color history. The underlying list has the original ActualPairSupply contract, including both source sides and their literal zero-error futures.", true),
        Node("ActualHistoryImage", ImageDefinition("history"),
            "This set contains exactly the original color histories obtained from the actual contract lists at the specified departure length.", true),
        Node("ActualSourceImage", ImageDefinition("source"),
            "The image uses the original full literal source constructor on a chosen side. Its prefix includes the original stem and the paid anchor precisely when the model is anchored; its tail is the prescribed original tail.", true),
        Node("ActualSourcePairImage", ImageDefinition("pair"),
            "The high and low sources are constructed from the same execution list and share its color history. The two respective literal future tails are retained.", true),
        Node("historyImageCount", ImageCountDefinition("history"),
            "This is the cardinality of the actual history image at observation length Nobs.", true),
        Node("sourceImageCount", ImageCountDefinition("source"),
            "This is the cardinality of one actual full-source image at observation length Nobs.", true),
        Node("sourcePairImageCount", ImageCountDefinition("pair"),
            "This is the cardinality of the actual same-list high and low source-pair image.", true),
        Node("actual_observation_count_correspondence", CorrespondenceStatement(),
            "The original reconstruction gives both the history length and each observed source-prefix length as Delta+T, with Delta=26 for the original model and Delta=52 for the anchored model. The equivalence fixes the return list itself. The original history parser is injective on all lists; the original source parser is injective at fixed list weight T. The high projection also makes the same-list source-pair map injective. Consequently all three image cardinalities are exactly the original contract count. The closed contract selects the weak dictionary precisely when o(0) is true, while strict and recordMargin select the strict dictionary. Every literal source in these images is a legal eventually-empty source with its actual record, and each supplied error is zero from the unobserved terminal onward."),
        Node("contract_even_raw_asymptotics", Parameters(All(RawAsymptotics(ContractCount(I("model"), I("contract"), EvenIndex)), B("model", Model), B("contract", Contract))),
            "The exact contract dictionary equivalence transfers the raw limit and its little-o error to every original contract and every endpoint ownership vector. No additional positive-rate assumption is required."),
        Node("observation_even_reindexing", ReindexStatement(),
            "Both literal offsets are even. The indices Delta+2v are cofinal. For every sufficiently large even observation length 2v, subtracting half the offset gives the nonnegative list half-weight v-Delta/2, and Delta+2(v-Delta/2)=2v. Thus the shifted indexing covers the entire eventual even observation support."),
        Node("actual_observation_length_asymptotics", ObservationAsymptoticsStatement(),
            "Each image count at Delta+T equals the actual contract count at T. On even T at least seventy-eight, the low filler makes all these raw image counts positive; odd observed lengths have no lists because the offset and every list weight are even. Multiplying the raw list quotient by T/(T+Delta), which tends to one, preserves eta_b. The exact cofinal inverse indexing then gives convergence on every sufficiently large even observed length Nobs, for histories, each original source side and the same-list pair. Subtracting eta_b times Nobs yields a little-o error relative to Nobs in every case."))));
}
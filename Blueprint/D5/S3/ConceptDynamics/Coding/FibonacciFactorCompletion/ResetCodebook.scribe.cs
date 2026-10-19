using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class ResetCodebookDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/ResetCodebook.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n),t);
    private static Formula All(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.ForAll,[..v],p);
    private static Formula Ex(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.Exists,[..v],p);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula And(params Formula[] p)
    {
        var r=p[^1];for(var k=p.Length-2;k>=0;--k)r=new Formula.Logic(p[k],FormulaLogicOperator.And,r);return r;
    }
    private static Formula Nat => I("Nat");
    private static Formula Int => I("Int");
    private static Formula Real => I("Real");
    private static Formula Returns => Call("List",I("Return"));
    private static Formula Letters => Call("List",I("CuLetter"));
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Words => Fn(Int,Letters);
    private static Formula Sequences => Fn(Int,I("CuLetter"));
    private static Formula Ap(Formula a, Formula b) => Call("apply",a,b);
    private static Formula Add(Formula a, Formula b) => Call("add",a,b);
    private static Formula Sub(Formula a, Formula b) => Call("subtract",a,b);
    private static Formula Mul(Formula a, Formula b) => Call("multiply",a,b);
    private static Formula Div(Formula a, Formula b) => Call("divide",a,b);
    private static Formula Pow(Formula a, Formula b) => Call("power",a,b);
    private static Formula Lt(Formula a, Formula b) => Call("lt",a,b);
    private static Formula Le(Formula a, Formula b) => Call("le",a,b);
    private static Formula Mem(Formula a, Formula b) => Call("member",a,b);
    private static Formula Len(Formula w) => Call("length",w);
    private static Formula Cast(Formula n) => Call("toInt",n);
    private static Formula Cut(Formula w, Formula j) => Call("blockCut",w,j);
    private static Formula Weight(Formula xs) => Call("listWeight",xs);
    private static Formula State(Formula w, Formula i) => Call("pastState",w,i);
    private static Formula Start(Formula m) => Call("initial",I("high"),m);
    private static Formula H => Call("hSide",I("high"));
    private static Formula A => Call("aSide",I("high"));
    private static Formula G => I("g");
    private static Formula Chi => I("chi");
    private static Formula Rho => I("rho");
    private static Formula Exec(Formula xs, Formula z) => Call("execute",I("high"),xs,z);
    private static Formula Trace(Formula k, Formula d, Formula xs, Formula z) => Call("GuardTrace",k,d,I("false"),I("high"),xs,z);
    private static Formula Threshold => Div(Div(Sub(I("lam"),I("b")),Pow(G,D(2))),Pow(Chi,I("K")));
    private static Formula ResetFloor => Sub(H,Mul(Pow(Rho,Call("m",I("R"))),Sub(H,Mul(Chi,A))));
    private static Formula Delta => Sub(ResetFloor,Start(I("sourceModel")));
    private static Formula Gamma => Mul(Delta,Pow(G,I("N")));
    private static Formula Scale => Mul(Pow(G,D(2)),Pow(Chi,I("K")));
    private static Formula Book => Call("Subtype",new Formula.Sequence(And(
        Trace(I("K"),Threshold,I("xs"),Start(I("sourceModel"))),Equal(Weight(I("xs")),I("N"))),I("xs"),Returns));
    private static Formula Epsilon => Div(Call("min",Sub(I("b"),Call("actualAutomaticCost",I("K"))),Mul(Scale,Gamma)),D(2));
    private static Formula W => new Formula.Sequence(Call("executionWord",Call("cons",I("R"),Call("val",Ap(I("choices"),I("j"))))),I("j"),Int);
    private static Formula GuardRun(Formula w, Formula i, Formula k) => All(
        Equal(Ap(w,Sub(i,Cast(I("q")))),I("c")),B("q",Call("Fin",k)));
    private static Formula NoLongRun(Formula w, Formula k) => All(Call("not",All(
        Equal(Ap(w,Add(I("i"),Cast(I("q")))),I("c")),B("q",Call("Fin",Add(k,D(1)))))),B("i",Int));
    private static Formula Tiled(Formula w, Formula omega) => All(Equal(
        Ap(omega,Add(Cut(w,I("j")),Cast(I("k")))),Call("getElem",Ap(w,I("j")),I("k"))),
        B("j",Int),B("k",Call("Fin",Len(Ap(w,I("j"))))));
    private static Formula CutFacts(Formula w) => And(Equal(Cut(w,D(0)),D(0)),All(Equal(
        Cut(w,Add(I("j"),D(1))),Add(Cut(w,I("j")),Cast(Len(Ap(w,I("j")))))),B("j",Int)),Call("StrictMono",Call("blockCut",w)));
    private static Formula Positive(Formula w) => All(Lt(D(0),Len(Ap(w,I("j")))),B("j",Int));
    private static Formula Budget => And(Le(D(2),I("K")),Lt(Sub(I("lam"),Mul(Scale,H)),I("b")),
        Lt(I("b"),Sub(I("lam"),Mul(Scale,Div(A,Sub(D(1),Mul(Rho,Pow(Chi,I("K")))))))));

    private static Formula CutDefinition(string name)
    {
        var w=I("W");var n=I("n");var j=I("j");
        if(name=="forwardCut" || name=="backwardCut")
        {
            var at=name=="forwardCut"?Cast(n):Call("negate",Add(Cast(n),D(1)));
            return Disp(All(And(Equal(Call(name,w,D(0)),D(0)),All(Equal(Call(name,w,Add(n,D(1))),
                Add(Call(name,w,n),Cast(Len(Ap(w,at))))),B("n",Nat))),B("W",Words)));
        }
        return Disp(All(And(All(Equal(Cut(w,Cast(n)),Call("forwardCut",w,n)),B("n",Nat)),
            All(Equal(Cut(w,Call("negSucc",n)),Call("negate",Call("backwardCut",w,Add(n,D(1))))),B("n",Nat))),B("W",Words)));
    }
    private static Formula WindowDefinition() => Disp(All(And(Equal(Call("blockWindow",I("W"),I("a"),D(0)),Call("nil")),
        All(Equal(Call("blockWindow",I("W"),I("a"),Add(I("n"),D(1))),Call("append",Ap(I("W"),I("a")),
            Call("blockWindow",I("W"),Add(I("a"),D(1)),I("n")))),B("n",Nat))),B("W",Words),B("a",Int)));
    private static Formula ChoiceDefinition() => Disp(All(And(Equal(Call("choiceWindow",I("choices"),I("a"),D(0)),Call("nil")),
        All(Equal(Call("choiceWindow",I("choices"),I("a"),Add(I("n"),D(1))),Call("cons",Ap(I("choices"),I("a")),
            Call("choiceWindow",I("choices"),Add(I("a"),D(1)),I("n")))),B("n",Nat))),B("V",I("Type")),B("choices",Fn(Int,I("V"))),B("a",Int)));
    private static Formula LowerDefinition() => Disp(All(Iff(Mem(I("omega"),Call("LowerMemoryLanguage",I("n"),I("K"),I("d"))),
        And(NoLongRun(I("omega"),I("K")),All(Imp(GuardRun(I("omega"),I("i"),I("K")),Lt(Mul(Pow(Chi,Sub(I("K"),D(1))),I("d")),
            Call("finitePast",I("omega"),I("i"),I("n"),D(0)))),B("i",Int)))),B("n",Nat),B("K",Nat),B("d",Real),B("omega",Sequences)));
    private static Formula TilingStatement() => Disp(All(Imp(Positive(I("W")),And(CutFacts(I("W")),
        Ex(Tiled(I("W"),I("omega")),B("omega",Sequences)))),B("W",Words)));
    private static Formula DifferenceStatement() => Disp(All(Equal(Sub(Exec(I("xs"),I("y")),Exec(I("xs"),I("x"))),
        Mul(Pow(G,Weight(I("xs"))),Sub(I("y"),I("x")))),B("xs",Returns),B("x",Real),B("y",Real)));
    private static Formula GainStatement() => Disp(All(Imp(And(Trace(I("K"),I("d"),I("xs"),Start(I("model"))),
        Equal(Weight(I("xs")),I("N")),Lt(Start(I("model")),I("B")),Le(I("B"),I("E"))),And(
            Trace(I("K"),Add(I("d"),Mul(Sub(I("B"),Start(I("model"))),Pow(G,I("N")))),I("xs"),I("E")),
            Lt(A,Exec(I("xs"),I("E"))))),B("K",Nat),B("N",Nat),B("d",Real),B("B",Real),B("model",I("Model")),B("xs",Returns),B("E",Real)));
    private static Formula FiniteJoint()
    {
        var execution=Call("resetConcatenation",I("R"),Call("map",I("val"),I("words")));
        return All(And(Trace(I("K"),Add(Threshold,Gamma),execution,Start(I("targetModel"))),
            Call("ActualPairSupply",I("targetModel"),I("o"),Sub(I("b"),Epsilon),I("strict"),execution)),
            B("targetModel",I("Model")),B("words",Call("List",Book)));
    }
    private static Formula FiniteConclusion()
    {
        var memory=Ex(And(Le(I("K"),I("n")),Lt(Mul(H,Pow(Rho,I("n"))),Mul(Pow(Chi,Sub(I("K"),D(1))),Gamma))),B("n",Nat));
        var tiles=All(And(CutFacts(W),Ex(Tiled(W,I("omega")),B("omega",Sequences))),B("choices",Fn(Int,Book)));
        return And(Lt(D(0),Delta),Lt(D(0),Gamma),Lt(D(0),Epsilon),FiniteJoint(),memory,tiles);
    }
    private static Formula BilateralConclusion()
    {
        var realization=Ex(And(Mem(I("omega"),Call("AuxiliaryLanguage",I("K"),Add(Threshold,Gamma))),
            Mem(I("omega"),Call("LowerMemoryLanguage",I("n"),I("K"),Threshold)),Tiled(W,I("omega")),
            All(Trace(I("K"),Add(Threshold,Gamma),Call("cons",I("R"),Call("val",Ap(I("choices"),I("j")))),
                State(I("omega"),Cut(W,I("j")))),B("j",Int))),B("omega",Sequences));
        return And(Lt(D(0),Delta),Lt(D(0),Gamma),Lt(D(0),Epsilon),FiniteJoint(),Ex(And(Le(I("K"),I("n")),
            Lt(Mul(H,Pow(Rho,I("n"))),Mul(Pow(Chi,Sub(I("K"),D(1))),Gamma)),
            All(realization,B("choices",Fn(Int,Book)))),B("n",Nat)));
    }
    private static Formula CodebookStatement(bool bilateral) => Disp(All(Imp(Budget,Ex(And(Equal(Call("r",I("R")),D(1)),
        Lt(Call("max",Call("max",Call("xSide",I("high")),Call("ySide",I("high"))),Threshold),ResetFloor),
        All(Imp(Lt(D(0),I("N")),bilateral?BilateralConclusion():FiniteConclusion()),B("sourceModel",I("Model")),B("N",Nat))),B("R",I("Return")))),
        B("o",I("Ownership")),B("b",Real),B("K",Nat)));
    private static Formula WindowPositions()
    {
        var win=Call("blockWindow",I("W"),I("a"),I("n"));var at=Add(I("a"),Cast(I("j")));
        var offset=Add(Call("toNat",Sub(Cut(I("W"),at),Cut(I("W"),I("a")))),I("k"));
        Formula Get(Formula w,Formula k)=>Call("getD",Call("getElemOption",w,k),I("u"));
        return Disp(All(Imp(Positive(I("W")),And(Equal(Cast(Len(win)),Sub(Cut(I("W"),Add(I("a"),Cast(I("n")))),Cut(I("W"),I("a")))),
            All(Imp(And(Lt(I("j"),I("n")),Lt(I("k"),Len(Ap(I("W"),at)))),Equal(Get(win,offset),Get(Ap(I("W"),at),I("k")))),B("j",Nat),B("k",Nat)))),
            B("W",Words),B("a",Int),B("n",Nat)));
    }
    private static Formula CompactStatement() => Disp(All(Imp(And(Le(D(1),I("K")),Positive(I("W")),
        All(Mem(Call("uPadding",Call("blockWindow",I("W"),I("a"),I("n"))),Call("AuxiliaryLanguage",I("K"),I("d"))),B("a",Int),B("n",Nat))),
        Ex(And(Mem(I("omega"),Call("AuxiliaryLanguage",I("K"),I("d"))),Tiled(I("W"),I("omega"))),B("omega",Sequences))),
        B("K",Nat),B("d",Real),B("W",Words)));
    private static Formula MemoryStatement() => Disp(All(Imp(And(Mem(I("omega"),Call("AuxiliaryLanguage",I("K"),Add(I("d"),I("gamma")))),
        Lt(Mul(H,Pow(Rho,I("n"))),Mul(Pow(Chi,Sub(I("K"),D(1))),I("gamma")))),Mem(I("omega"),Call("LowerMemoryLanguage",I("n"),I("K"),I("d")))),
        B("omega",Sequences),B("n",Nat),B("K",Nat),B("d",Real),B("gamma",Real)));
    private static DocumentBlock Node(string name,Formula formula,string prose,bool definition=false) => Describe.Lean(
        DescribeId.Create("fib-reset-codebook-"+name.Replace('_','-').ToLowerInvariant()),DeclarationHandle.Create(Prefix+name),H(name.Replace('_',' ')),
        StatementSource.FromAuthor(formula),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),definition?DescribeRole.Definition:DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common reset and exact weighted gain support finite actual records and bilateral lower-memory realizations.",H("Reset codebooks on one bilateral realization"),Blocks(
        Node("forwardCut",CutDefinition("forwardCut"),"Forward cuts add the next block's positive letter length.",true),
        Node("backwardCut",CutDefinition("backwardCut"),"Backward cuts sum the blocks at indices minus one, minus two and so on.",true),
        Node("blockCut",CutDefinition("blockCut"),"The origin is fixed. Negative cuts use the negative backward sum; negSucc(n) denotes minus n minus one.",true),
        Node("positive_block_tiling",TilingStatement(),"Every indexed family of nonempty words determines disjoint consecutive block intervals covering all integer letter positions. Each prescribed letter belongs to one bilateral sequence, even when block letter lengths vary."),
        Node("execute_seed_difference",DifferenceStatement(),"The original literal affine maps give the exact gain g raised to the original list weight. Positive return exponents make that weight even."),
        Node("exact_guard_gain",GainStatement(),"An initial gain at least B minus the original initial displacement remains at least that gain times g to the full word weight at every high return prefix. The same execution also stays above the original lower boundary."),
        Node("reset_codebook_construction",CodebookStatement(false),"The codebook subtype contains all weak original execution lists of weight N. One low reset R is fixed before both models and all weights. Its floor B is h minus rho to m(R) times h minus chi A; delta is B minus the selected original initial displacement and gamma is delta times g to N. Every finite joint choice has the exact high guard d plus gamma and the displayed common actual error margin. The margin uses the original automatic-slot bound, and the literal zero-error futures are included in ActualPairSupply. The two-sided symbolic tiling uses exactly the same reset blocks."),
        Node("blockWindow",WindowDefinition(),"A finite window concatenates the blocks at a through a+n-1 in increasing execution order.",true),
        Node("block_window_positions",WindowPositions(),"The finite window has precisely the difference of its endpoint cuts as its length. Each internal block letter occurs at the cut difference plus its local index."),
        Node("compact_block_tiling",CompactStatement(),"Centered finite block windows, shifted to their prescribed cuts, lie in one compact auxiliary language. A convergent subsequence preserves every eventually fixed block letter and the same closed guard. The result is one bilateral realization of the entire two-sided choice."),
        Node("LowerMemoryLanguage",LowerDefinition(),"The lower graph forbids K+1 consecutive c letters and checks the zero-seed past before the current Kth c transition. Membership retains the original strict inequality and the original high-edge timing.",true),
        Node("uniform_guard_lower_memory",MemoryStatement(),"The bilateral state exceeds its zero-seed n-past by at most h times rho to n. A common state margin larger than that error gives every strict lower-graph guard on the same sequence."),
        Node("choiceWindow",ChoiceDefinition(),"A finite window of indexed choices keeps their order and their actual subtype membership.",true),
        Node("bilateral_reset_codebook",CodebookStatement(true),"One reset floor exceeds both actual initial states and d. For the full weak equal-weight original codebook, the finite actual supply retains the positive displayed half-minimum error margin. Fix delta and gamma first and then choose n at least K with h rho to n less than chi to K-1 times gamma. Every two-sided choice uses that same reset and has one bilateral sequence in AuxiliaryLanguage at d plus gamma and in the original lower-memory language at d. Every reset block occurs at its prescribed cut, and its complete return trace on that same sequence has high-start margin gamma. Thus the before-Kth-c state margin is chi to K-1 times delta times g to N. The weighted factor-count and factor-rate conclusions follow from the counting argument."))));
}

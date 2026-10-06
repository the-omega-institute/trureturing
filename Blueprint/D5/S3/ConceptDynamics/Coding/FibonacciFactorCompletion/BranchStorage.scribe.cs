using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class BranchStorageDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/BranchStorage.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) => new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] vars) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
    private static Formula Ex(Formula body, params Formula.BoundVariable[] vars) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. vars], body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; --i)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula List(Formula a) => Call("List", a);
    private static Formula Ap(Formula f, Formula x) => Call("apply", f, x);
    private static Formula Add(Formula a, Formula b) => Call("add", a, b);
    private static Formula Mul(Formula a, Formula b) => Call("multiply", a, b);
    private static Formula Sub(Formula a, Formula b) => Call("subtract", a, b);
    private static Formula Pow(Formula a, Formula b) => Call("power", a, b);
    private static Formula Len(Formula a) => Call("length", a);
    private static Formula At(Formula a, Formula p) => Call("getElem", a, p);
    private static Formula Nat => I("Nat");
    private static Formula Labels => List(I("Label"));
    private static Formula Colors => List(I("Color"));
    private static Formula Address(Formula a) => Call("address", a);
    private static Formula Coord(Formula a, Formula p) => Call("coordinate", a, p);
    private static Formula Append(Formula a, Formula b) => Call("append", a, b);
    private static Formula Syn(Formula p, Formula r, Formula z) => Call("synchronousPrefix", p, r, z);
    private static Formula Record(Formula a, Formula r) => Call("OperationRecord", I("o"), I("b"), I("closed"), a, r);
    private static Formula Frame(Formula c, Formula q, Formula o) => Call("Frame", c, q, o);
    private static Formula Run(Formula r, Formula t) => Call("Run", I("action"), Call("full", r),
        Frame(I("initialConfiguration"), D(0), I("nil")), t);
    private static Formula Reach(Formula horizon, Formula c) => Call("ReachThrough", I("action"),
        I("initialConfiguration"), Call("OperationRecordPredicate", I("o"), I("b"), I("closed")), horizon, c);
    private static Formula Peak(Formula horizon) => Call("Peak", I("action"), I("initialConfiguration"),
        Call("OperationRecordPredicate", I("o"), I("b"), I("closed")), I("encoding"), horizon);
    private static Formula ZType => Fn(Call("Fin", I("n")), I("Bool"));
    private static Formula CutType => Call("FrameType", I("Configuration"), I("Label"));
    private static Formula Horizon => Add(Len(I("P")), Mul(I("n"), I("L")));
    private static Formula HighPrefix => Syn(I("P"), I("U"), I("z"));
    private static Formula LowPrefix => Syn(I("Q"), I("V"), I("z"));
    private static Formula ColorPrefix => Syn(I("h"), I("W"), I("z"));
    private static Formula High => Address(Append(HighPrefix, I("w1")));
    private static Formula Low => Address(Append(LowPrefix, I("w2")));
    private static Formula HighRecord => Call("recordWithTail", I("o"), ColorPrefix, I("w1"));
    private static Formula LowRecord => Call("recordWithTail", I("o"), ColorPrefix, I("w2"));
    private static Formula Cut => Ap(I("cuts"), I("z"));
    private static Formula State => Call("state", Cut);
    private static Formula Output => Call("output", Cut);
    private static Formula Path(Formula s, Formula w, Formula path)
    {
        var p=I("p"); var next=Add(p,D(1));
        return And(Equal(Ap(path,D(0)),s),
            All(Equal(Call("nextGuard",Ap(path,p),Ap(Address(w),p)),Call("some",Ap(path,next))),B("p",Nat)),
            All(Call("InSupport",Ap(path,p),Coord(w,p)),B("p",Nat)),
            All(Equal(Coord(w,p),Call("branch",Ap(Address(w),p),Coord(w,next))),B("p",Nat)));
    }
    private static Formula Splice(Formula a, Formula w, Formula path, Formula tailPath)
    {
        var p=I("p"); var at=Add(Len(a),p); var whole=Append(a,w);
        return And(Path(I("G0"),whole,path),All(And(
            Equal(Ap(Address(whole),at),Ap(Address(w),p)),Equal(Coord(whole,at),Coord(w,p)),
            Equal(Ap(path,at),Ap(tailPath,p))),B("p",Nat)));
    }
    private static Formula Contracts()
    {
        var a=I("a");var r=I("r");var t=I("frame");var p=I("p");
        var safety=All(Imp(And(Record(a,r),Run(r,t),Call("lt",p,Len(Call("output",t)))),
            Equal(At(Call("output",t),p),Ap(a,p))),B("a",Fn(Nat,I("Label"))),
            B("r",Fn(Nat,I("Color"))),B("frame",CutType),B("p",Nat));
        var live=All(Imp(And(Record(a,r),Call("OperationFiniteSource",a)),
            Ex(And(Run(r,t),Call("lt",p,Len(Call("output",t)))),B("frame",CutType))),
            B("a",Fn(Nat,I("Label"))),B("r",Fn(Nat,I("Color"))),B("p",Nat));
        var current=Frame(I("c"),I("q"),I("out"));
        var after=Frame(I("d"),Add(I("q"),D(1)),Append(I("out"),I("batch")));
        var post=All(Imp(And(Record(a,r),Run(r,current),Equal(Ap(I("action"),I("c")),Call("acquire",I("f"))),
            Equal(Ap(I("f"),Ap(r,I("q"))),Call("some",Call("pair",I("d"),I("batch"))))),
            Ex(Call("Drain",I("action"),after,t),B("frame",CutType))),
            B("a",Fn(Nat,I("Label"))),B("r",Fn(Nat,I("Color"))),B("c",I("Configuration")),
            B("d",I("Configuration")),B("q",Nat),B("out",Labels),B("batch",Labels),
            B("f",Fn(I("Color"),Call("Option",Call("Product",I("Configuration"),Labels)))));
        var faithful=All(Imp(And(Ex(Reach(I("H"),I("c")),B("H",Nat)),
            Ex(Reach(I("H"),I("d")),B("H",Nat)),Equal(Ap(I("encoding"),I("c")),Ap(I("encoding"),I("d")))),
            Equal(I("c"),I("d"))),B("c",I("Configuration")),B("d",I("Configuration")));
        return And(safety,live,post,faithful);
    }
    private static Formula Hypotheses()
    {
        var i=I("i");var p=I("p");var ui=Ap(I("U"),i);var vi=Ap(I("V"),i);var wi=Ap(I("W"),i);
        return And(Call("LegalWord",I("G0"),I("s1"),I("P")),Call("LegalWord",I("G0"),I("s2"),I("Q")),
            Equal(Len(I("P")),Len(I("h"))),Equal(Len(I("Q")),Len(I("h"))),Call("lt",D(0),I("L")),
            All(And(Call("LegalWord",I("s1"),I("s1"),ui),Call("LegalWord",I("s2"),I("s2"),vi),
                Equal(Len(ui),I("L")),Equal(Len(vi),I("L")),Equal(Len(wi),I("L"))),B("i",I("Bool"))),
            Call("notEqual",Ap(I("U"),I("false")),Ap(I("U"),I("true"))),
            Call("notEqual",Ap(I("V"),I("false")),Ap(I("V"),I("true"))),
            Call("le",Call("familyEndpointBudget",I("P"),I("Q"),I("h"),I("U"),I("V"),I("W"),I("L")),I("b")),
            Call("lt",I("k"),Len(I("P"))),All(Imp(Call("lt",p,I("k")),Equal(At(I("P"),p),At(I("Q"),p))),B("p",Nat)),
            Call("notEqual",At(I("P"),I("k")),At(I("Q"),I("k"))),Contracts());
    }
    private static Formula ConstructedFamilies()
    {
        var p=I("p");var at=Add(Horizon,p);var stem=Call("take",I("P"),I("k"));
        var alignment=All(And(Equal(Ap(High,at),Ap(Address(I("w1")),p)),
            Equal(Coord(Append(HighPrefix,I("w1")),at),Coord(I("w1"),p)),
            Equal(Ap(Low,at),Ap(Address(I("w2")),p)),Equal(Coord(Append(LowPrefix,I("w2")),at),Coord(I("w2"),p)),
            Equal(Ap(HighRecord,at),Call("observe",I("o"),Coord(I("w1"),p),D(0))),
            Equal(Ap(LowRecord,at),Call("observe",I("o"),Coord(I("w2"),p),D(0)))),B("z",ZType),B("p",Nat));
        var injection=All(Imp(Equal(Call("address",Append(Syn(I("P"),I("U"),I("z")),I("w1"))),
            Call("address",Append(Syn(I("P"),I("U"),I("zprime")),I("w1")))),Equal(I("z"),I("zprime"))),
            B("z",ZType),B("zprime",ZType));
        var cuts=All(And(Call("Cut",I("action"),I("initialConfiguration"),Call("front",HighRecord,Horizon),Cut),
            Call("le",Len(Output),I("k")),Equal(Output,Call("take",stem,Len(Output))),Call("IsPrefix",Output,stem),
            Reach(Horizon,State)),B("z",ZType));
        var joint=All(Imp(Equal(Call("pair",State,Output),Call("pair",Call("state",Ap(I("cuts"),I("zprime"))),
            Call("output",Ap(I("cuts"),I("zprime"))))),Equal(I("z"),I("zprime"))),B("z",ZType),B("zprime",ZType));
        var members=All(new Formula.Logic(Call("member",I("c"),I("states")),FormulaLogicOperator.Iff,
            Ex(Equal(State,I("c")),B("z",ZType))),B("c",I("Configuration")));
        var capacity=All(Imp(Call("le",Peak(Horizon),Call("toWithTop",I("B"))),
            Call("le",Pow(D(2),I("n")),Mul(Sub(Pow(D(2),Add(I("B"),D(1))),D(1)),Add(I("k"),D(1))))),B("B",Nat));
        return All(Ex(And(All(And(Record(High,HighRecord),Call("OperationFiniteSource",High),Record(Low,LowRecord)),B("z",ZType)),
            alignment,injection,cuts,joint,members,Call("le",Pow(D(2),I("n")),Mul(Call("card",I("states")),Add(I("k"),D(1)))),capacity),
            B("cuts",Fn(ZType,CutType)),B("states",Call("Finset",I("Configuration")))),B("n",Nat));
    }
    private static Formula Conclusion()
    {
        var fixedPaths=Ex(And(Path(I("s1"),I("w1"),I("tailPath1")),Path(I("s2"),I("w2"),I("tailPath2")),
            All(Ex(And(Splice(HighPrefix,I("w1"),I("path1"),I("tailPath1")),
                Splice(LowPrefix,I("w2"),I("path2"),I("tailPath2"))),B("path1",Fn(Nat,I("Guard"))),B("path2",Fn(Nat,I("Guard")))),
                B("n",Nat),B("z",ZType))),B("tailPath1",Fn(Nat,I("Guard"))),B("tailPath2",Fn(Nat,I("Guard"))));
        var floor=Call("toReal",Call("natDivide",Sub(I("H"),Len(I("P"))),I("L")));
        var loss=Call("logb",D(2),Call("toReal",Add(I("k"),D(1))));
        var bound=All(Imp(And(Call("le",Len(I("P")),I("H")),Call("le",Peak(I("H")),Call("toWithTop",I("B")))),
            Call("le",Sub(Sub(floor,D(1)),loss),Call("toReal",I("B")))),B("H",Nat),B("B",Nat));
        var ratio=Call("sequenceByH",I("H"),Call("divide",Call("ENatToENNReal",Peak(I("H"))),Call("toENNReal",I("H"))));
        var rate=Call("le",Call("ofReal",Call("divide",D(1),Call("toReal",I("L")))),Call("liminfAtTop",ratio));
        var vertices=All(Imp(And(Record(I("a"),I("r")),Call("Trace",I("action"),Call("full",I("r")),
            Frame(I("initialConfiguration"),D(0),I("nil")),I("frame"),I("vertices")),Call("le",Call("acquired",I("frame")),I("H")),
            Call("member",I("c"),I("vertices"))),Call("le",Call("toWithTop",Len(Ap(I("encoding"),I("c")))),Peak(I("H")))),
            B("a",Fn(Nat,I("Label"))),B("r",Fn(Nat,I("Color"))),B("frame",CutType),B("vertices",List(I("Configuration"))),B("H",Nat),B("c",I("Configuration")));
        return Ex(And(Call("LegalWord",I("s1"),I("e1"),I("w1")),Call("LegalWord",I("s2"),I("e2"),I("w2")),
            Call("lt",Call("canonicalReturnLo",I("U"),I("L")),Coord(I("w1"),D(0))),Call("lt",Coord(I("w1"),D(0)),Call("canonicalReturnHi",I("U"),I("L"))),
            Call("lt",Call("canonicalReturnLo",I("V"),I("L")),Coord(I("w2"),D(0))),Call("lt",Coord(I("w2"),D(0)),Call("canonicalReturnHi",I("V"),I("L"))),
            fixedPaths,ConstructedFamilies(),bound,rate,vertices),B("e1",I("Guard")),B("e2",I("Guard")),B("w1",Labels),B("w2",Labels));
    }
    private static Formula Statement() => Disp(All(Imp(Hypotheses(),Conclusion()),
        B("Configuration",I("Type")),B("action",Fn(I("Configuration"),Call("Op",I("Configuration"),I("Color"),I("Label")))),
        B("initialConfiguration",I("Configuration")),B("o",I("Ownership")),B("b",I("Real")),B("s1",I("Guard")),B("s2",I("Guard")),
        B("P",Labels),B("Q",Labels),B("h",Colors),B("U",Fn(I("Bool"),Labels)),B("V",Fn(I("Bool"),Labels)),
        B("W",Fn(I("Bool"),Colors)),B("L",Nat),B("k",Nat),B("encoding",Fn(I("Configuration"),List(I("Bool"))))));

    private static Formula PathDefinition() => Disp(All(new Formula.Logic(
        Call("LiteralTailPath",I("s"),I("w"),I("path")),FormulaLogicOperator.Iff,Path(I("s"),I("w"),I("path"))),
        B("s",I("Guard")),B("w",Labels),B("path",Fn(Nat,I("Guard")))));
    private static Formula SpliceDefinition() => Disp(All(new Formula.Logic(
        Call("LiteralTailSplice",I("A"),I("w"),I("path"),I("tailPath")),FormulaLogicOperator.Iff,
        Splice(I("A"),I("w"),I("path"),I("tailPath"))),B("A",Labels),B("w",Labels),
        B("path",Fn(Nat,I("Guard"))),B("tailPath",Fn(Nat,I("Guard")))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two nondegenerate return hulls give fixed actual tails and complete storage lower bounds.",
        H("Nondegenerate competing branches and complete storage"),
        Blocks(Describe.Lean(DescribeId.Create("fib-literal-tail-path"),DeclarationHandle.Create(Prefix+"LiteralTailPath"),
            H("A complete actual literal tail path"),StatementSource.FromAuthor(PathDefinition()),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The finite word is continued by L0 forever. The predicate retains the initial guard, every edge, coordinate support and the affine source recurrence."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fib-literal-tail-splice"),DeclarationHandle.Create(Prefix+"LiteralTailSplice"),
            H("The same literal scalar and guard future after a prefix"),StatementSource.FromAuthor(SpliceDefinition()),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The prefix length shifts all three components of the fixed tail. The guard and scalar laws hold at every natural position, including the unobserved departure seam."))),DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fib-nondegenerate-branch-storage"),
            DeclarationHandle.Create(Prefix+"nondegenerate_branch_storage"),H("Actual paired tails at every first disagreement"),
            StatementSource.FromAuthor(Statement()),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("synchronousPrefix(P,U,z)=P++choiceBlocks(U,List.ofFn(z)). OperationRecordPredicate(o,b,closed) is the original actual record relation at the closed error budget b. The same two finite literal tails and their guard paths are chosen before every natural depth and Boolean history. Both scalar endpoints lie strictly inside their canonical hulls. Interior transport obtains actual colors for every ownership assignment at the complete six-group endpoint budget; closed-relaxation feasibility alone is not used as an owned-endpoint assertion.")),
                Paragraph(Text("LiteralTailPath(s,w,path) states the initial guard, every actual guard edge, coordinate support and affine recurrence. LiteralTailSplice(A,w,path,tailPath) states this full source law for A++w and exact shifted literal, scalar and guard equality with the same tail. The displayed formula expands both predicates. Empty choice histories are included. The stems agree before arbitrary k and differ at k. Safety and positionwise finite-source liveness on these target competitors force acquisition before output k, and hence finite startup; no separate startup assumption is supplied.")),
                Paragraph(Text("Equal-length block extraction gives the first-source injection. Both actual records share the entire acquired past; the first record has one fixed literal future. The common-stem cut gives 2^n<=card(states)*(k+1). Joint state and output separation, with at most k+1 output prefixes, yields 2^n<=(2^(B+1)-1)*(k+1) under a finite complete Peak bound B. sequenceByH(H,E) denotes the sequence H mapped to E. The encoding is injective on every configuration reachable on any actual record; all intermediate readable vertices are included. The emitted prefix is a finite external count, with readable output-side information included in the configuration.")),
                Paragraph(Text("For every H>=length(P), the bound is floor((H-length(P))/L)-1-logb(2,k+1)<=B. Natural subtraction and integer division are retained. Monotonicity fills all observation horizons, and finite or infinite peaks give liminf Peak(H)/H>=1/L. This is a necessary coefficient for each compliant decoder. The competing singleton, optional original-piece restriction and bilateral auxiliary codebook remain separate mathematical cases."))),DescribeRole.Theorem))));
}

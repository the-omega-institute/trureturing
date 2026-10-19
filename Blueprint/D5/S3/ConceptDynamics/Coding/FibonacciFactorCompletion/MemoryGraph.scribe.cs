using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class MemoryGraphDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/MemoryGraph.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.ForAll, [..v], p);
    private static Formula Ex(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.Exists, [..v], p);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(params Formula[] p) { var r=p[^1]; for(var k=p.Length-2;k>=0;--k) r=new Formula.Logic(p[k],FormulaLogicOperator.And,r); return r; }
    private static Formula Nat => I("Nat");
    private static Formula Int => I("Int");
    private static Formula Real => I("Real");
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Seq => Fn(Int,I("CuLetter"));
    private static Formula Vertex => Call("MemoryVertex",I("n"));
    private static Formula Vertices => Fn(Int,Vertex);
    private static Formula Letters => Call("List",I("CuLetter"));
    private static Formula Ap(Formula f, Formula x) => Call("apply",f,x);
    private static Formula Add(Formula a, Formula b) => Call("add",a,b);
    private static Formula Sub(Formula a, Formula b) => Call("subtract",a,b);
    private static Formula Mul(Formula a, Formula b) => Call("multiply",a,b);
    private static Formula Pow(Formula a, Formula b) => Call("power",a,b);
    private static Formula Lt(Formula a, Formula b) => Call("lt",a,b);
    private static Formula Le(Formula a, Formula b) => Call("le",a,b);
    private static Formula Lambda(string n,Formula t,Formula p) => new Formula.Sequence(p,I(n),t);
    private static Formula Window(Formula i) => Call("memoryWindow",I("n"),I("omega"),i);
    private static Formula Shift(Formula v,Formula a) => Call("memoryShift",v,a);
    private static Formula Path(Formula p,Formula omega) => Call("BilateralGraphPath",I("side"),I("K"),I("d"),p,omega);
    private static Formula Live(Formula v) => Call("LiveVertex",I("side"),I("K"),I("d"),v);
    private static Formula Walk(Formula v,Formula w) => Call("RetainedWalk",I("side"),I("K"),I("d"),v,w);
    private static Formula Edge(Formula v,Formula a,Formula t) => Call("MemoryEdge",I("side"),I("K"),I("d"),v,a,t);
    private static Formula Language => Call("MemoryLanguage",I("side"),I("n"),I("K"),I("d"));
    private static Formula Len(Formula w) => Call("length",w);
    private static Formula Val(Formula v) => Call("val",v);
    private static Formula IntCast(Formula x) => Call("toInt",x);
    private static Formula At(Formula w,Formula k) => Call("getElem",w,k);
    private static Formula Sum(string name,Formula type,Formula body) => Call("sum",Lambda(name,type,body));
    private static Formula SourceParams(Formula body) => All(body,B("side",I("MemorySide")),B("n",Nat),B("K",Nat),B("d",Real));
    private static Formula WindowValue() => Disp(All(Equal(Call("memoryValue",Window(I("i")),I("z")),Call("finitePast",I("omega"),I("i"),I("n"),I("z"))),B("n",Nat),B("omega",Seq),B("i",Int),B("z",Real)));
    private static Formula WindowShift() => Disp(All(Equal(Window(Add(I("i"),D(1))),Shift(Window(I("i")),Ap(I("omega"),I("i")))),B("n",Nat),B("omega",Seq),B("i",Int)));
    private static Formula Reconstruction() => Disp(All(Imp(All(Equal(Ap(I("p"),Add(I("i"),D(1))),Shift(Ap(I("p"),I("i")),Ap(I("omega"),I("i")))),B("i",Int)),Equal(I("p"),Call("memoryWindow",I("n"),I("omega")))),B("n",Nat),B("p",Vertices),B("omega",Seq)));
    private static Formula Run() => Disp(All(Imp(And(Lt(D(0),I("r")),Le(I("r"),Add(I("n"),D(1)))),Iff(Call("memoryRun",Window(I("i")),Ap(I("omega"),I("i")),I("r")),All(Equal(Ap(I("omega"),Sub(I("i"),IntCast(I("k")))),I("c")),B("k",Call("Fin",I("r")))))),B("n",Nat),B("r",Nat),B("omega",Seq),B("i",Int)));
    private static Formula Reversal()
    {
        Formula No(bool forward) => All(Call("not",All(Equal(Ap(I("omega"),forward?Add(I("i"),IntCast(I("k"))):Sub(I("i"),IntCast(I("k")))),I("c")),B("k",Call("Fin",Add(I("K"),D(1)))))),B("i",Int));
        return Disp(All(Iff(No(true),No(false)),B("K",Nat),B("omega",Seq)));
    }
    private static Formula Correspondence() => Disp(SourceParams(All(Imp(And(Lt(D(0),I("K")),Le(I("K"),I("n"))),Iff(Call("member",I("omega"),Language),Call("existsUnique",Lambda("p",Vertices,Path(I("p"),I("omega")))))),B("omega",Seq))));
    private static Formula Prepend() => Disp(SourceParams(All(Imp(And(Live(I("v")),Path(I("p"),I("omega")),Equal(Ap(I("p"),D(0)),I("t")),Edge(I("v"),I("a"),I("t"))),Ex(And(Path(I("q"),I("nu")),Equal(Ap(I("q"),D(0)),I("v")),Equal(Ap(I("nu"),D(0)),I("a")),All(Imp(Le(D(0),I("i")),Equal(Ap(I("nu"),Add(I("i"),D(1))),Ap(I("omega"),I("i")))),B("i",Int))),B("q",Vertices),B("nu",Seq))),B("v",Vertex),B("t",Vertex),B("a",I("CuLetter")),B("p",Vertices),B("omega",Seq))));
    private static Formula Extension() => Disp(SourceParams(All(Imp(Walk(I("v"),I("w")),Ex(And(Path(I("p"),I("omega")),Equal(Ap(I("p"),D(0)),I("v")),All(Equal(Ap(I("omega"),IntCast(I("k"))),At(I("w"),I("k"))),B("k",Call("Fin",Len(I("w")))))),B("p",Vertices),B("omega",Seq))),B("v",Vertex),B("w",Letters))));
    private static Formula Segment() => Disp(SourceParams(All(Imp(And(Path(I("p"),I("omega")),All(Equal(Ap(I("omega"),Add(I("i"),IntCast(I("k")))),At(I("w"),I("k"))),B("k",Call("Fin",Len(I("w")))))),Walk(Ap(I("p"),I("i")),I("w"))),B("p",Vertices),B("omega",Seq),B("w",Letters),B("i",Int))));
    private static Formula Count()
    {
        var dictionary=Call("RetainedPathDictionary",I("side"),I("n"),I("K"),I("d"),I("T"));
        var paths=Call("NatCard",dictionary); var factors=Call("factorCount",Language,I("T"));
        return Disp(SourceParams(All(Imp(And(Lt(D(0),I("K")),Le(I("K"),I("n"))),And(Call("Finite",dictionary),Le(factors,paths),Le(paths,Mul(Pow(D(2),I("n")),factors)))),B("T",Nat))));
    }
    private static Formula Weighted()
    {
        var core=Call("CoreVertex",I("side"),I("n"),I("K"),I("d"));
        var choices=Fn(Call("Fin",I("k")),Call("Product",I("CuLetter"),core));
        var labels=Call("ofFn",Lambda("i",Call("Fin",I("k")),Call("fst",Ap(I("choices"),I("i")))));
        var source=All(Imp(Call("CorePath",I("side"),I("K"),I("d"),I("k"),I("v"),I("choices")),Walk(Val(I("v")),labels)),B("k",Nat),B("v",core),B("choices",choices));
        var matrix=Call("weightedAdjacency",I("side"),I("n"),I("K"),I("d"),I("z"));
        var equality=All(Equal(Sum("t",core,Call("matrixEntry",Pow(matrix,I("k")),I("v"),I("t"))),Sum("choices",choices,Call("coreMonomial",I("side"),I("K"),I("d"),I("z"),I("k"),I("v"),I("choices")))),B("k",Nat),B("v",core));
        return Disp(SourceParams(All(And(source,equality),B("z",Real))));
    }
    private static DocumentBlock Node(string name,Formula statement,string prose) => Describe.Lean(DescribeId.Create("fib-memory-graph-"+name.Replace('_','-')),DeclarationHandle.Create(Prefix+name),H(name.Replace('_',' ')),StatementSource.FromAuthor(statement),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(prose))),DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original lower and upper finite-memory source languages are exactly the bilateral labels of a finite directed graph, whose retained paths have the original weighted adjacency expansion.",
        H("Original finite-memory directed graphs"),Blocks(
        Paragraph(Text("A vertex is a function from Fin n to the original c/u alphabet. Index zero holds the most recent past letter. Reversing these indices gives the chronological n-letter word. A transition inserts its label at index zero and drops the oldest letter. The seed composition uses the original high-side letter maps. A current run of K+1 c letters is forbidden. At the current Kth c, the lower graph requires a strict zero-seed bound; the upper graph requires a nonstrict h-seed bound. Both use the original threshold chi to K-1 times d.")),
        Node("window_value",WindowValue(),"The graph seed composition equals finitePast on the actual n-letter past, for every real seed and integer position."),
        Node("window_shift",WindowShift(),"Moving one integer position inserts exactly the current letter into the past window."),
        Node("path_memory_reconstruction",Reconstruction(),"Induction on each finite memory coordinate reconstructs it from the bilateral label sequence. No arbitrary memory annotation survives the shift equations."),
        Node("window_run",Run(),"For positive run lengths up to n+1, the finite memory test is exactly the run ending at the current position, including the current letter."),
        Node("forbidden_run_reversal",Reversal(),"Reversing the K+1 indices converts the original forward forbidden block into the equivalent current-ending block without changing the sequence."),
        Node("original_memory_graph_correspondence",Correspondence(),"For n at least K and positive K, each original lower or upper sequence has exactly one bilateral graph path. Conversely every graph path has the reconstructed actual past windows and precisely the original guard at the current Kth c. All thresholds d remain in scope."),
        Node("prepend_bilateral_path",Prepend(),"A retained start supplies a genuine left past. One allowed edge joins it to a genuine right future at the edge target. The joined path preserves the selected label and every future letter."),
        Node("retained_walk_extension",Extension(),"Every finite path through retained vertices has an actual two-sided extension. Induction joins one edge at a time and preserves every finite word letter. Empty paths and transient bridges are included; strong connectivity is unnecessary."),
        Node("bilateral_path_segment",Segment(),"Any finite word occurring on one bilateral path gives a retained walk starting at its actual vertex. Translation supplies the required bilateral realization of each visited vertex."),
        Node("original_weighted_path_count",Count(),"For every total weight T, the complete retained path dictionary is finite. Forgetting the initial vertex maps onto the original factor dictionary. A path is determined by its word and initial n-letter vertex, so its count is between the factor count and 2 to n times that count. Weight zero and unsupported weights retain the same formulas."),
        Node("original_weighted_adjacency_paths",Weighted(),"The matrix is indexed by precisely the vertices appearing on bilateral paths. Its entry sums z to letterWeight(a) over all original allowed labels with those endpoints, including parallel labels. Each complete labeled path contributes z to its total original wordWeight; a disallowed path contributes zero. Matrix powers sum these monomials exactly. The empty path contributes one. Every allowed path supplies a retained word in the same graph, which has a two-sided extension by the preceding theorem. Identifying the convergence boundary with a unique spectral-radius-one root, and then identifying that root with the weighted factor rate, are separate conclusions."))));
}

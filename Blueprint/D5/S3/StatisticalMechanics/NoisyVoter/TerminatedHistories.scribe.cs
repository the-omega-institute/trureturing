using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.NoisyVoter;

internal sealed class TerminatedHistoriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite terminated graphical histories meet exactly when their native source labels agree.",
        H("Terminated native graphical histories"),
        Blocks(
            Paragraph(Text("Fix a simple graph G on an arbitrary vertex type V, a sample type O, the native coordinate family x, and one sample z. A choice coordinate at v takes values in the actual neighbour set of v. The function step(x,z) sends (k+1,v) to (k,J(k+1,v)) when its refresh control is false, and returns none at time zero or at a true refresh control. The list history(x,n,v,z) starts with (n,v), follows precisely these selected edges, and stops at the first refresh or time zero, including that terminal vertex. Its recursion is on the natural starting time, so the list is finite without any finiteness assumption on V.")),
            Paragraph(Text("labelVertex sends an initial label at v to (0,v), and a fresh label at the strictly positive time k to (k,v). This map is injective: positive fresh times cannot coincide with initial time zero. The predicate Meets(x,z,n,m,v,w) means that some absolute space-time pair p belongs to both actual history lists. It is defined independently of source labels and opinion values. Different backward offsets are allowed to name that same p.")),
            Describe.Lean(DescribeId.Create("voter-terminated-history-source-correspondence"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/NoisyVoter/TerminatedHistories.terminated_history_source_correspondence"),
                H("Native terminal coordinates, complete common suffixes, and coalescence"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(
                    "D5/L/StatisticalMechanics/benjaminihelmantovzhukovskii2023noisyvoter")),
                Blocks(
                    Paragraph(Text("All n and m are arbitrary finite natural starting times, and v and w are arbitrary starting vertices. In the formula, index reads an optional list entry, last is getLast?, drop deletes a prefix, and some and none are the Option constructors. The pair projections fst and snd retain actual absolute time and vertex. The second history has the same starting, edge and stopping properties by the same universal statement with its parameters substituted.")),
                    Paragraph(Text("The suffix extraction law proves, at every actual offset i, that dropping the first i vertices gives the full history started at the vertex read there. It is established by induction on the native starting time: a stopped singleton permits only offset zero, while a nonrefreshing successor reduces every positive offset to the selected predecessor. This law is used to compare the terminal coordinates of the original history and every visited history. Consequently, histories that meet have the same source; equality of sources puts their common terminal vertex in both lists. A meeting at any intermediate vertex also identifies the entire remaining ordered lists, including the stopping vertex.")),
                    Paragraph(Text("The last vertex is exactly labelVertex(source(x,n,v,z)), and step is none there. Thus initial and positive fresh terminals have their original disjoint interpretation. The native_source theorem reconstructs the opinion as the coin at that source. Equality of the two Boolean opinion values is a different event: different initial vertices can carry the same initial opinion while their singleton histories and their labels remain distinct."))),
                DescribeRole.Theorem),
            Paragraph(Text("For the synchronous noisy voter law, take the same G, x and z used by its native recursion: I(v)=x(initial(v),z), F(k,v)=x(fresh(k,v),z), R(k,v)=x(refresh(k,v),z), and J(k,v)=x(choice(k,v),z), with k positive in the auxiliary coordinates. No time-zero auxiliary coordinate is read. Every connected locally finite simple graph with nonempty actual neighbour sets, finite or infinite, is within this statement. No graph cardinality, common horizon, additional probability law, coupling or terminal-correctness premise is required. The original independence, measurability and marginal-law assumptions may be retained; this correspondence holds for every individual realization.")),
            Paragraph(Text("At time zero the history is the singleton initial vertex. An immediate refresh is a singleton positive-time history. With no refresh before zero the complete selected path ends in an initial label. The statement also includes identical starts, unequal starting times, distinct starts, either terminal kind and meetings at different backward offsets. It does not assert a variance identity or a survival-probability estimate."))), []));

    private static Formula X(string n) => F.Id(n);
    private static Formula Named(string n) => Seq(Operatorname, Grp(X(n)));
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Named(n), [.. args]);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iffn(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, b, Close);
    private static Formula Point() => Seq(Nat(), Times, Sp, X("V"));
    private static Formula Some(Formula a) => Call("some", a);
    private static Formula Hist(Formula n, Formula v) => Call("history", X("x"), n, v, X("z"));
    private static Formula Src(Formula n, Formula v) => Call("source", X("x"), n, v, X("z"));
    private static Formula Index(Formula h, Formula i, Formula p) => Eqn(Call("index", h, i), Some(p));
    private static Formula Statement()
    {
        var a = Hist(X("n"), X("v"));
        var b = Hist(X("m"), X("w"));
        var sa = Src(X("n"), X("v"));
        var sb = Src(X("m"), X("w"));
        var terminal = Call("labelVertex", sa);
        var common = Hist(Call("fst", X("p")), Call("snd", X("p")));
        var edges = All("i", Nat(), All("p", Point(), All("q", Point(),
            Imp(Index(a, X("i"), X("p")),
                Imp(Index(a, Seq(X("i"), Plus, D(1)), X("q")),
                    Eqn(Call("step", X("x"), X("z"), X("p")), Some(X("q"))))))));
        var suffixes = All("i", Nat(), All("j", Nat(), All("p", Point(),
            Imp(Index(a, X("i"), X("p")), Imp(Index(b, X("j"), X("p")),
                And(Eqn(Call("drop", a, X("i")), common), Eqn(Call("drop", b, X("j")), common)))))));
        var coalescence = Iffn(Eqn(sa, sb), Call("Meets", X("x"), X("z"), X("n"), X("m"), X("v"), X("w")));
        var commonTerminal = Imp(Eqn(sa, sb),
            And(Mem(terminal, a), And(Mem(terminal, b), Eqn(Call("last", a), Call("last", b)))));
        var result = And(Index(a, D(0), Pair(X("n"), X("v"))),
            And(edges, And(Eqn(Call("last", a), Some(terminal)),
                And(Eqn(Call("step", X("x"), X("z"), terminal), Named("none")),
                    And(suffixes, And(coalescence, commonTerminal))))));
        var coords = Seq(Open, X("c"), Colon, Call("Coord", X("V")), Close, Sp, To, Sp,
            Arr(X("O"), Call("Value", X("G"), X("c"))));
        return Disp(All("V", Named("Type"), All("O", Named("Type"),
            All("G", Call("SimpleGraph", X("V")), All("x", coords, All("z", X("O"),
                All("n", Nat(), All("m", Nat(), All("v", X("V"), All("w", X("V"), result))))))))));
    }
}

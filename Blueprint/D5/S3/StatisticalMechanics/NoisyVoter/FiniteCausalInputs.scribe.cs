using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.NoisyVoter;

internal sealed class FiniteCausalInputsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/NoisyVoter/FiniteCausalInputs.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/benjaminihelmantovzhukovskii2023noisyvoter");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite positive-time inputs determine the joint native opinion and source history.",
        H("Finite causal inputs and joint history laws"),
        Blocks(
            Paragraph(Text("Let G be a locally finite simple graph, with an arbitrary vertex type. The input set at time zero and vertex v consists of the initial opinion at v. At time n+1 it consists of the fresh opinion, refresh control and neighbour choice at (n+1,v), together with the input sets at time n of all actual neighbours of v. This is a finite set on finite and infinite graphs. Taking its union over times zero through N gives historyInputs(u,N). No fresh, refresh or choice coordinate at time zero occurs.")),
            Paragraph(Text("The history records both the actual synchronous opinion and its disjoint initial-or-fresh source label at each time. Its opinion coordinate is the original nvm recursion; its label coordinate is the original source recursion. The finite vector restrictInputs retains all input coordinates jointly. To decode it, complete the unspecified coordinates using an arbitrary fixed assignment base and run those same recursions. The resulting history is independent of that completion.")),
            Node("factorization", "finite_history_factorization", "Finite reconstruction of the complete joint history", Factorization(),
                "For every locally finite simple graph, every sample type, every base assignment, root and natural horizon, all inputs are initial or have positive time, and decoding the finite input vector recovers the joint history at every sample point. Agreement propagates through the same refresh decision and the same selected neighbour in the preceding time layer. The statement includes horizon zero and requires no probability, stationarity or independence assumption."),
            Node("joint-law", "history_law_of_positive_coordinate_laws", "The positive-time coordinate law determines the joint history law", LawTransport(),
                "The two coordinate families may live on different measurable spaces with different measures. On each space, require mutual independence of the family indexed by initial and strictly positive-time coordinates, measurability of those coordinates, and the same prescribed marginal laws. Then the complete joint opinion-and-source history laws agree, using the same graph, root and horizon. Neither measurability nor independence nor a marginal law is required for a fresh, refresh or choice coordinate at time zero. The common marginal family is arbitrary and may be specialized to fair opinion coins, noisy refresh controls and uniform choices on the actual neighbour sets."),
            Paragraph(Text("For repetition observations with lag d at times i and i+d, the horizon N=t+d includes every observation, including the empty repetition sum at t=0. Retaining source labels jointly also retains every equality among sources, rather than identifying sources whenever their opinion colours happen to agree. The result transports the full source partition and does not assert independence of source collisions.")),
            Paragraph(Text("Specializing the marginal family to the original coordinateLaw gives the joint law of the repetition statistic W, the source-collision count C and the multiplicity of each fixed unordered pair of distinct labels. Each is a readout of the joint history through horizon t+d. For arbitrary vertex types, measurability follows by extending the readout from the deterministic finite image of the decoder as a finite sum of measurable singleton indicators; it does not require a globally measurable equality relation on all pairs of labels. The positive-coordinate product realization may fill unused time-zero coordinates arbitrarily and has the same history law as the native full-coordinate product realization.")),
            Paragraph(Text("This finite reconstruction supplies the finite-coordinate determination assertion in the opening paragraph of the proof of Theorem 2.1 in the ancestral-collision source. The recursive input set is used directly; no identification with the displayed graph ball or countability conclusion is asserted. The exact variance decomposition with both the variance of the collision count and the expected squared pair multiplicities, its two remainder identities, and its almost-sure equality criterion require further arguments. Equality of the finite product input laws is obtained from the specified independence and marginals, and the common deterministic decoder then transports it to the joint history."))), []));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("voter-causal-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula X(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula DepArr(string name, Formula type, Formula body) =>
        Seq(Open, X(name), Colon, type, Close, Sp, To, Sp, body);
    private static Formula Inst(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Coord() => Call("Coord", X("V"));
    private static Formula Value() => Call("Value", X("G"), X("c"));
    private static Formula Assignment(string sample) => DepArr("c", Coord(), Arr(X(sample), Value()));
    private static Formula BaseType() => DepArr("c", Coord(), Value());
    private static Formula Inputs() => Call("historyInputs", X("u"), X("N"));
    private static Formula History(string family) => Call("history", X(family), X("u"), X("N"));
    private static Formula Restriction(string family) => Call("restrictInputs", X(family), X("u"), X("N"));
    private static Formula Map(string measure, Formula function) => Call("map", X(measure), function);
    private static Formula PositiveCoords() => Seq(OpenBrace, X("c"), Colon, Coord(), Bar,
        Call("positive", X("c")), CloseBrace);
    private static Formula Val() => Call("val", X("c"));
    private static Formula PositiveFamily(string family) => Seq(Open, LambdaLower, Sp, X("c"), Colon,
        PositiveCoords(), Sp, Mapsto, Sp, App(X(family), Val()), Close);
    private static Formula Graph(Formula body) => All("G", Call("SimpleGraph", X("V")),
        Inst(Seq(X("G"), Dot, Named("LocallyFinite")), body));
    private static Formula RootHorizon(Formula body) =>
        All("base", BaseType(), All("u", X("V"), All("N", Nat(), body)));

    private static Formula Factorization()
    {
        var membership = new Formula.Relation(X("c"), FormulaRelationOperator.MemberOf, Inputs());
        var positivity = All("c", Coord(), Imp(membership, Call("positive", X("c"))));
        var decoded = Call("decode", X("base"), X("u"), X("N"), App(Restriction("x"), X("w")));
        var factorization = All("x", Assignment("O"), All("w", X("O"),
            Eqn(App(History("x"), X("w")), decoded)));
        return Disp(All("V", Named("Type"), All("O", Named("Type"),
            Graph(RootHorizon(And(positivity, factorization))))));
    }

    private static Formula LawTransport()
    {
        var hx = All("c", Coord(), Imp(Call("positive", X("c")),
            Call("Measurable", App(X("x"), X("c")))));
        var hy = All("c", Coord(), Imp(Call("positive", X("c")),
            Call("Measurable", App(X("y"), X("c")))));
        var hix = Call("iIndepFun", PositiveFamily("x"), X("P"));
        var hiy = Call("iIndepFun", PositiveFamily("y"), X("Q"));
        var hlx = All("c", PositiveCoords(), Call("HasLaw", App(X("x"), Val()),
            App(X("m"), X("c")), X("P")));
        var hly = All("c", PositiveCoords(), Call("HasLaw", App(X("y"), Val()),
            App(X("m"), X("c")), X("Q")));
        var law = Eqn(Map("P", History("x")), Map("Q", History("y")));
        var marginals = DepArr("c", PositiveCoords(), Call("Measure", Call("Value", X("G"), Val())));
        var body = All("u", X("V"), All("N", Nat(), law));
        body = Imp(hlx, Imp(hly, body));
        body = Imp(hix, Imp(hiy, body));
        body = Imp(hx, Imp(hy, body));
        body = All("m", marginals, body);
        body = All("x", Assignment("O"), All("y", Assignment("Oprime"), body));
        body = All("P", Call("Measure", X("O")), All("Q", Call("Measure", X("Oprime")), body));
        return Disp(All("V", Named("Type"), All("O", Named("Type"), All("Oprime", Named("Type"),
            Graph(Inst(Call("MeasurableSpace", X("O")),
                Inst(Call("MeasurableSpace", X("Oprime")), body)))))));
    }
}

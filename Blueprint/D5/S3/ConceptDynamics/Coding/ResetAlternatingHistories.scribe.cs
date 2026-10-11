using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResetAlternatingHistoriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll,
        [B("q", I("Nat")), B("hq", Call("NatPositive", I("q")))], body);
    private static Formula EvenAll(Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll,
        [B("q", I("Nat")), B("hq", Call("NatPositive", I("q"))),
         B("he", Call("Even", I("q")))], body);
    private static Formula For(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, type);
    private static Formula At(Formula x, Formula t) => Call("coordinate", x, t);
    private static Formula Matrix => Call("resetMatrix", I("q"));
    private static Formula Graph => Call("expandedGraph", Matrix);
    private static Formula Histories => Call("History", Graph);
    private static Formula BoundaryMatrix => Add(Call("identityMatrix", I("Sign"), I("q")), Matrix);
    private static Formula BoundaryGraph => Call("expandedGraph", BoundaryMatrix);
    private static Formula BoundaryEdges => Call("product", Call("Edge", BoundaryMatrix), I("Sign"));
    private static Formula Data => Call("resetNumberedData", I("q"), I("hq"));
    private static Formula Squares => Call("squares", Data);
    private static Formula Forgetting => Call("resetFiniteForgetting", I("q"), I("hq"), I("he"));
    private static Formula Homeomorph => Call("resetAlternatingWholeRayHomeomorph", I("q"), I("hq"), I("he"));
    private static Formula Pair => Call("resetAlternatingTablePair", I("q"), I("hq"));
    private static Formula Local => Call("resetAlternatingTablesLocal", I("q"), I("hq"), I("he"));
    private static Formula Representative(Formula r) =>
        Call("resetRayRepresentative", I("q"), I("hq"), I("alpha"), I("n"), r);
    private static Formula Past(Formula x, Formula alpha) => For(
        Implies(new Formula.Relation(I("k"), FormulaRelationOperator.LessThanOrEqual, I("n")),
            Equal(At(x, I("k")), At(alpha, I("k")))), B("k", I("Int")));
    private static Formula Ray(Formula alpha) => Seq(OpenBrace,
        I("y"), Colon, Histories, Sp, Bar, Sp, Past(I("y"), alpha), CloseBrace);
    private static Formula Out => Seq(OpenBrace,
        I("r"), Colon, BoundaryEdges, Sp, Bar, Sp,
        Equal(Call("source", BoundaryGraph, I("r")),
            Call("target", Graph, At(I("alpha"), I("n")))), CloseBrace);
    private static Formula Union => Seq(
        new Formula.Subscript(Cup, Seq(I("r"), Sp, InMacro, Sp, Out)),
        Sp, Ray(Representative(I("r"))));
    private static Formula AlternatingGraph => Call("expandedGraph", Call("resetMatrix", I("q")));
    private static Formula AlternatingPair => Call("TablePair", AlternatingGraph, AlternatingGraph,
        Num(0), I("q"), I("q"), Num(0));
    private static Formula AlternatingPairDefinition => All(AlternatingPair);
    private static Formula AlternatingLocalTheorem => new Formula.BindMany(FormulaQuantifier.ForAll,
        [B("q", I("Nat")), B("hq", Call("NatPositive", I("q"))),
         B("he", Call("Even", I("q")))],
        Call("LocalCriterion", Call("resetAlternatingTablePair", I("q"), I("hq"))));
    private static Formula WholeRays => EvenAll(For(
        And(Equal(Call("image", Homeomorph, Ray(I("alpha"))), Union),
            And(For(Equal(Call("target", Graph, At(Representative(I("r")), I("n"))),
                    Call("target", BoundaryGraph, Call("value", I("r")))), B("r", Out)),
                And(For(Implies(NotEqual(I("r"), I("s")),
                        Call("Disjoint", Ray(Representative(I("r"))), Ray(Representative(I("s"))))),
                        B("r", Out), B("s", Out)),
                    For(Implies(Past(I("y"), Representative(I("r"))),
                        new Formula.BindMany(FormulaQuantifier.Exists, [B("x", Histories)],
                            And(Past(I("x"), I("alpha")),
                                And(Equal(Call("apply", Homeomorph, I("x")), I("y")),
                                    Equal(Call("boundary", Call("leftLift", Squares, Forgetting, I("x")), I("n")),
                                        Call("value", I("r"))))))),
                        B("r", Out), B("y", Histories))))),
        B("alpha", Histories), B("n", I("Int"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Alternating numbered reset squares yield finite-window tables and a disjoint same-cut decomposition of whole past rays.",
        H("Alternating reset histories and whole rays"),
        Blocks(
            Paragraph(Text("NatPositive(q) means 0 < q. Sign is Multiplicative Bool with XOR addition. Matrix means resetMatrix q, Graph means expandedGraph Matrix, and Histories means History Graph with the native product and subtype topologies. The boundary matrix is literally the identity matrix plus Matrix, over the same natural Boolean group algebra. All edge numbers and absolute group coordinates are retained.")),
            Paragraph(Text("The names resetNumberedData, resetFiniteForgetting and resetExpandedEssential denote Alternating.resetNumberedData, Alternating.resetFiniteForgetting and Alternating.reset_expanded_essential in the ResetNumberedHistories namespace. resetAlternatingTablesLocal denotes reset_alternating_tables_local. The other displayed reset names are the same public names in that namespace.")),
            Describe.Lean(DescribeId.Create("reset-alternating-table-pair"),
                DeclarationHandle.Create(Prefix + "resetAlternatingTablePair"),
                H("Uniform alternating table pair on the actual reset graph"),
                StatementSource.FromAuthor(Disp(AlternatingPairDefinition)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive q the definition returns TablePair Graph Graph 0 q q 0. Its forward and backward tables read q+1 original numbered edges. The D, F and legal A boundary constructors distinguish identity, reset and advance; the guarded FD/AF squares preserve the endpoints."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reset-alternating-tables-local"),
                DeclarationHandle.Create(Prefix + "reset_alternating_tables_local"),
                H("Even positive q gives the local criterion"),
                StatementSource.FromAuthor(Disp(AlternatingLocalTheorem)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive even q, the criterion gives both seams on legal q+2-edge words and both center roundtrips on legal 2q+1-edge words. The left and right comparison ranks contract along their respective sweeps; overlapping strips identify the windows and recover the original center edge."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reset-numbered-square-data"),
                DeclarationHandle.Create(Prefix + "resetNumberedData"),
                H("Squares on the actual numbered additive boundary"),
                StatementSource.FromAuthor(Disp(All(Typed(Data,
                    Call("NumberedData", Matrix, Matrix, BoundaryMatrix))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The local square interface uses Edge(identityMatrix + resetMatrix) times Sign as its boundary type. Its source and target are the original expanded boundary endpoints. The two summands occupy disjoint coefficient-number intervals; labels, numbers and absolute signs determine the boundary equivalence."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reset-finite-forgetting"),
                DeclarationHandle.Create(Prefix + "resetFiniteForgetting"),
                H("Forgetting after q squares"),
                StatementSource.FromAuthor(Disp(EvenAll(Typed(Forgetting,
                    Call("FiniteForgetting", Squares, I("q")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("FiniteForgetting is the existing positive-length, left and right forgetting proposition on unrestricted natural-indexed square strips. Equality of the left input strips forces the initial boundaries to coincide after q squares; equality of the right input strips forces the terminal boundaries to coincide. The last common input edge supplies the terminal source equality used by the left contraction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reset-expanded-essential"),
                DeclarationHandle.Create(Prefix + "reset_expanded_essential"),
                H("Every positive reset graph is essential"),
                StatementSource.FromAuthor(Disp(All(Call("Essential", Graph)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every expanded vertex has an outgoing reset edge. Incoming to suffix zero uses reset with the opposite absolute sign; incoming to a positive suffix uses the predecessor advance with the same sign. Positivity is the only hypothesis, so q=1 is included."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reset-generic-table-equality"),
                DeclarationHandle.Create(Prefix + "reset_generic_H_eq_applyTable"),
                H("The square lift equals the finite table map"),
                StatementSource.FromAuthor(Disp(EvenAll(For(
                    Equal(Call("H", Squares, Forgetting, I("x")),
                        Call("applyTable", Graph, Graph, Call("forward", Pair), Call("seamG", Local), I("x"))),
                    B("x", Histories))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The equality holds on every legal bilateral history. A q+1-square window of the full generic lift is compared with the original forward sweep. Both sides retain the same numbered expanded edge at each integer coordinate. forward denotes the f field of the table pair; seamG is the seam field of reset_alternating_tables_local."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reset-whole-ray-homeomorphism"),
                DeclarationHandle.Create(Prefix + "resetAlternatingWholeRayHomeomorph"),
                H("The native history homeomorphism"),
                StatementSource.FromAuthor(Disp(EvenAll(Typed(Homeomorph,
                    Call("Homeomorph", Histories, Histories))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is Squares.historyHomeomorph applied to the actual reset numbered data and its q-square finite forgetting. Both histories carry their original product and subtype topology."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reset-ray-representative"),
                DeclarationHandle.Create(Prefix + "resetRayRepresentative"),
                H("A full representative for each numbered boundary"),
                StatementSource.FromAuthor(Disp(All(For(Typed(Representative(I("r")), Histories),
                    B("alpha", Histories), B("n", I("Int")), B("r", Out))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive q, every full history alpha and integer cut n, r is the subtype of full numbered boundary edges with absolute group coordinate whose source equals the target of alpha at n. The representative is NumberedData.beta using the essential reset graph. Its arbitrary legal future extends the prescribed right past; no even hypothesis is needed to define it. A subtype value is denoted value(r)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("reset-even-same-cut-whole-rays"),
                DeclarationHandle.Create(Prefix + "reset_even_same_cut_whole_rays"),
                H("Exact disjoint decomposition and every future preimage"),
                StatementSource.FromAuthor(Disp(WholeRays)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every ray in the formula fixes all numbered expanded coordinates at all integers k <= n, including negative times. image is literal set image under the homeomorphism and the union ranges over the exact source-constrained numbered boundary subtype. The four conjuncts state the entire image equality at the same cut, the actual endpoint of every representative, pairwise disjointness for unequal full boundary indices, and a preimage for every legal right future with the original alpha past and exactly that boundary value at n. The preimage boundary is read from Squares.leftLift with the same finite-forgetting proof."))),
                DescribeRole.Theorem))));
}

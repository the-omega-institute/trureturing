using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class PinedaSeparatingWeightsRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/pinedamontoya2026separatingweights");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted paths obstruct each of the three universal separating-weight analogues.",
        H("Separating weights for three graph operators"),
        Blocks(
            Paragraph(Text("Separation requires a separable characteristic polynomial, nonzero coordinates in every nonzero right eigenvector, and pairwise distinct coordinates in the specified modes. The nonzero-coordinate requirement includes the zero eigenspace. Weights are real and strictly positive on actual unordered edges or ordered arcs. Each support has its own polynomial and its own degree.")),
            Definition("normalized", "Normalized Laplacian analogue", "NormalizedClaim",
                Undirected(NormalizedSeparation()),
                "The operator is the symmetric normalized Laplacian I minus the adjacency matrix scaled on both sides by inverse square-root degrees. The symbol s(i,j) denotes the unordered pair in the edge subtype when i and j are adjacent. The eigenvectors are real. For the distinct-coordinate requirement the modes are orthogonal to the vector of square-root degrees."),
            Definition("adjacency", "Adjacency analogue", "AdjacencyClaim",
                Undirected(AdjacencySeparation()),
                "The symmetric weighted adjacency has one variable per unordered edge and zero entries off the support. The symbol s(i,j) denotes the unordered pair in the edge subtype when i and j are adjacent. The eigenvectors are real. The distinct-coordinate requirement applies when the adjacency has a strictly larger eigenvalue."),
            Definition("directed", "Directed Laplacian analogue", "DirectedClaim",
                Directed(),
                "The loopless digraph contains a spanning out-arborescence. Path in T means a directed quiver path using the arcs of T, with the empty path allowed at the root. Rows receive arcs, so entry (i,j) of the adjacency reads the arc from j to i. The receiving-degree Laplacian is the diagonal row-sum matrix minus that adjacency, with entries then embedded in the complex numbers. The distinct-coordinate requirement applies at nonzero eigenvalues."),
            Definition("claim", "Question 7.5", "claim",
                new Formula.Logic(C("NormalizedClaim"), FormulaLogicOperator.Or,
                    new Formula.Logic(C("AdjacencyClaim"), FormulaLogicOperator.Or, C("DirectedClaim"))),
                "An affirmative answer to any of the three universal analogues would imply this disjunction."),
            Refutation("normalized-refuted", "The normalized Laplacian obstruction", "normalized_refuted",
                "NormalizedClaim",
                "The five-vertex path has consecutive weights a, b, c, d and row degrees a, a+b, b+c, c+d, d. Scale the coordinates of (bd, 0, −ad, 0, ac) by the square roots of these degrees. The resulting nonzero vector is an eigenvector at 1 and vanishes at vertices 1 and 3, indexed from zero."),
            Refutation("adjacency-refuted", "The adjacency obstruction", "adjacency_refuted",
                "AdjacencyClaim",
                "On the same path the weighted adjacency annihilates the nonzero vector (bd, 0, −ad, 0, ac). The zero coordinates at vertices 1 and 3 violate separation for every positive weighting."),
            Refutation("directed-refuted", "The receiving-degree Laplacian obstruction", "directed_refuted",
                "DirectedClaim",
                "The out-path on vertices 0, 1, 2 has arcs 0 to 1 and 1 to 2, of weights p and q. The receiving-degree Laplacian has rows (0,0,0), (−p,p,0), (0,−q,q). Its last coordinate vector is a right eigenvector at q and its first two coordinates vanish."),
            Refutation("result", "Refutation of the three analogues", "result", "claim",
                "On each of the indicated supports the nonvanishing implication would force the polynomial to vanish on the whole positive orthant. The real polynomial identity theorem on the product of positive intervals and the injective integer coefficient map force the original polynomial to be zero. This argument applies at every degree and uses only the nonzero-coordinate requirement.",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("pineda-montoya-et-al-2026-separating-weights-question-7-5"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string id, string title, string name, Formula body, string prose) =>
        Describe.Lean(DescribeId.Create("pineda-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(Rel(C(name), FormulaRelationOperator.Equal, Parens(body)))),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Refutation(string id, string title, string name, string proposition, string prose,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("pineda-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(new Formula.Not(C(proposition)))),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem, resolution);

    private static Formula Undirected(Formula separation) =>
        OnVertices("SimpleGraph", graph => Imp(Member(graph, "Connected"),
            Let("E", Member(graph, "edgeSet"), Certificate(separation))));

    private static Formula Directed()
    {
        Formula i = F.Id("i"), j = F.Id("j"), vertices = F.Id("V");
        return OnVertices("Digraph", graph =>
        {
            Formula loopless = All("i", vertices, new Formula.Not(Adjacent(graph, i, i)));
            Formula arcs = Seq(Left, OpenBrace,
                Rel(Pair(i, j), FormulaRelationOperator.MemberOf, Seq(vertices, Sp, Times, Sp, vertices)),
                Sp, Mid, Sp, Adjacent(graph, i, j), Right, CloseBrace);
            return Imp(loopless, Lines(
                Seq(Parens(SpanningOutArborescence(graph)), Sp, Rightarrow),
                Let("E", arcs, Certificate(DirectedSeparation()))));
        });
    }

    private static Formula OnVertices(string graphType, Func<Formula, Formula> body) =>
        All("n", Blackboard("N"),
            Imp(Rel(D(2), FormulaRelationOperator.LessThanOrEqual, F.Id("n")),
                Let("V", Call("Fin", F.Id("n")),
                    All("G", Call(graphType, F.Id("V")), body(F.Id("G"))))));

    private static Formula SpanningOutArborescence(Formula graph)
    {
        Formula tree = F.Id("T"), vertices = F.Id("V");
        Formula paths = App(new Formula.Subscript(C("Path"), tree), F.Id("r"), F.Id("v"));
        Formula uniquePaths = Ex("r", vertices, All("v", vertices,
            Ex("p", paths, All("q", paths, Equal(F.Id("q"), F.Id("p"))))));
        return Ex("T", Call("Digraph", vertices),
            Lines(Seq(Rel(tree, FormulaRelationOperator.LessThanOrEqual, graph), Sp, Land), uniquePaths));
    }

    private static Formula Certificate(Formula separation)
    {
        Formula index = F.Id("E"), p = F.Id("P"), w = F.Id("w");
        Formula eval = Seq(C("MvPolynomial"), Dot, new Formula.Subscript(C("eval"), D(2)));
        Formula cast = App(Member(C("Int"), "castRingHom"), Blackboard("R"));
        Formula ev = App(eval, Parens(cast), w, p);
        Formula positive = All("e", index,
            Rel(D(0), FormulaRelationOperator.LessThan, App(w, F.Id("e"))));
        Formula criterion = new Formula.Logic(Parens(separation), FormulaLogicOperator.Iff,
            Nonzero(ev));
        return Ex("d", Blackboard("N"), Ex("P", Call("MvPolynomial", index, new Formula.Integers()),
            Lines(
                Seq(Nonzero(p), Sp, Land, Sp, App(Member(p, "IsHomogeneous"), F.Id("d")), Sp, Land),
                All("w", new Formula.TypeArrow(index, Blackboard("R")),
                    Lines(Seq(Parens(positive), Sp, Rightarrow), Parens(criterion))))));
    }

    private static Formula NormalizedSeparation()
    {
        Formula a = F.Id("A"), i = F.Id("i"), j = F.Id("j"), m = F.Id("M");
        Formula factor = F.Id("h");
        Formula normalizedEntries = Entries(new Formula.Fraction(
            App(a, i, j), Multiply(App(factor, i), App(factor, j))));
        Formula mode = Equal(SumOver("i", Multiply(App(factor, i), App(F.Id("x"), i))), D(0));
        return Let("A", WeightedAdjacency(),
            Let("h", Seq(i, Sp, Mapsto, Sp, Seq(Sqrt, Grp(SumOver("j", App(a, i, j))))),
                Let("M", new Formula.Binary(F.Id("I"), FormulaBinaryOperator.Subtract, normalizedEntries),
                    Separating(m, Blackboard("R"), mode))));
    }

    private static Formula AdjacencySeparation()
    {
        Formula a = F.Id("A"), mu = F.Id("mu"), real = Blackboard("R");
        Formula mode = Ex("mu", real, new Formula.Logic(Call("HasEigenvalue", a, mu),
            FormulaLogicOperator.And, Rel(F.Id("lambda"), FormulaRelationOperator.LessThan, mu)));
        return Let("A", WeightedAdjacency(), Separating(a, real, mode));
    }

    private static Formula DirectedSeparation()
    {
        Formula i = F.Id("i"), j = F.Id("j"), a = F.Id("A"), m = F.Id("M");
        Formula receivingAdjacency = Entries(If(Adjacent(F.Id("G"), j, i), App(F.Id("w"), Pair(j, i))));
        Formula diagonal = Call("diag",
            Seq(i, Sp, Mapsto, Sp, SumOver("j", App(a, i, j))));
        Formula receivingLaplacian = new Formula.Binary(diagonal, FormulaBinaryOperator.Subtract, a);
        return Let("A", receivingAdjacency,
            Let("M", Call("Complexify", receivingLaplacian),
                Separating(m, Blackboard("C"), Nonzero(F.Id("lambda")))));
    }

    private static Formula Separating(Formula matrix, Formula field, Formula mode)
    {
        Formula x = F.Id("x"), lambda = F.Id("lambda"), vertices = F.Id("V");
        Formula rightEigenvector = new Formula.Logic(Nonzero(x), FormulaLogicOperator.And,
            Equal(Multiply(matrix, x), Multiply(lambda, x)));
        Formula vectors = new Formula.TypeArrow(vertices, field);
        Formula s1 = Call("Separable", Call("charpoly", matrix));
        Formula s2 = All("lambda", field, All("x", vectors,
            Imp(rightEigenvector, All("i", vertices, Nonzero(App(x, F.Id("i")))))));
        Formula s3 = All("lambda", field, All("x", vectors,
            Imp(rightEigenvector, Imp(mode, Call("Injective", x)))));
        return Lines(s1, Seq(Land, Sp, Parens(s2)), Seq(Land, Sp, Parens(s3)));
    }

    private static Formula WeightedAdjacency()
    {
        Formula i = F.Id("i"), j = F.Id("j");
        return Entries(If(Adjacent(F.Id("G"), i, j), App(F.Id("w"), App(F.Id("s"), i, j))));
    }

    private static Formula C(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Member(Formula obj, string name) => Seq(obj, Dot, C(name));
    private static Formula Parens(Formula formula) => Seq(Open, formula, Close);
    private static Formula Blackboard(string symbol) => Seq(Mathbb, Grp(F.Id(symbol)));
    private static Formula Pair(Formula left, Formula right) => Seq(Open, left, Comma, right, Close);
    private static Formula Adjacent(Formula graph, Formula i, Formula j) => App(Member(graph, "Adj"), i, j);
    private static Formula If(Formula condition, Formula value) =>
        Seq(C("if"), Sp, condition, Sp, C("then"), Sp, value, Sp, C("else"), Sp, D(0));
    private static Formula Entries(Formula entry) =>
        new Formula.Subscript(Seq(OpenBracket, entry, CloseBracket), Seq(
            F.Id("i"), Comma, Rel(F.Id("j"), FormulaRelationOperator.MemberOf, F.Id("V"))));
    private static Formula SumOver(string variable, Formula term) =>
        Seq(new Formula.Subscript(Sum, Rel(F.Id(variable), FormulaRelationOperator.MemberOf, F.Id("V"))),
            Sp, term);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Lines(params Formula[] rows) =>
        new Formula.Aligned([.. rows.Select(row => Seq(Amp, row))]);
    private static Formula Let(string variable, Formula value, Formula body) =>
        Lines(Seq(C("let"), Sp, F.Id(variable), Sp, Colon, Eq, Sp, value, Sp, C("in")), body);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(C(name), args);
    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);
    private static Formula All(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.Exists, name, type, body);
    private static Formula Rel(Formula lhs, FormulaRelationOperator relation, Formula rhs) =>
        new Formula.Relation(lhs, relation, rhs);
    private static Formula Equal(Formula left, Formula right) => Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Nonzero(Formula formula) => Rel(formula, FormulaRelationOperator.NotEqual, D(0));
    private static Formula Imp(Formula lhs, Formula rhs) =>
        new Formula.Logic(Parens(lhs), FormulaLogicOperator.Implies, Parens(rhs));
}

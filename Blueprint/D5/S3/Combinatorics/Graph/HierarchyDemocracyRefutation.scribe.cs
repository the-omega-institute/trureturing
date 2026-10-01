using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class HierarchyDemocracyRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/moutsinas2021hierarchy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A weakly connected directed graph on six vertices with twelve unweighted arcs has forward hierarchical levels (227, -991, -991, 329, 767, 659)/2694 and forward democracy coefficient 901/898, which is larger than 1. This refutes Conjecture 3.6 of G. Moutsinas, C. Shuaib, W. Guo and S. Jarvis (arXiv:1908.04358), which asserts that the democracy coefficients of every weakly connected directed graph are at most 1.",
        H("A directed graph with democracy coefficient above one"),
        Blocks(
            Node("indeg", "The weighted in-degree", IndegFormula(),
                "For a matrix A of non-negative arc weights on n vertices, with a_ij > 0 exactly when there is an arc from i to j, the weighted in-degree of vertex j is d_j, the sum over i of a_ij.",
                "indeg", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("lap", "The transposed in-degree Laplacian", LapFormula(),
                "M is the transpose of the in-degree Laplacian L = diag(d) - A.",
                "lapT", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("residual", "The squared residual", ResidualFormula(),
                "For a vector x in R^n, the squared residual is the squared Euclidean norm of M x - d.",
                "residual", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("levels", "Forward hierarchical levels", LevelsFormula(),
                "A vector g is a vector of forward hierarchical levels when it minimizes the residual and, among all minimizers of the residual, has the least Euclidean norm.",
                "IsForwardLevels", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("democracy", "The forward democracy coefficient", DemocracyFormula(),
                "The forward democracy coefficient is 1 minus the mean of the differences g_j - g_i over the arcs from i to j, the mean being weighted by a_ij.",
                "forwardDemocracy", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("weak", "Weak connectivity", WeakFormula(),
                "A is weakly connected when the undirected simple graph on the n vertices, in which distinct vertices i and j are adjacent exactly when a_ij > 0 or a_ji > 0, is connected.",
                "WeaklyConnected", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 3.6", ClaimFormula(),
                "The forward half of the first bullet of Conjecture 3.6: for every n and every matrix A of non-negative weights with zero diagonal whose arcs form a weakly connected graph, every vector g of forward hierarchical levels gives a forward democracy coefficient at most 1.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A graph with coefficient 901/898", Disp(new Formula.Not(F.Id("claim"))),
                "Take n = 6 and the unweighted arcs 1 -> 4, 1 -> 5, 2 -> 6, 3 -> 6, 4 -> 5, 4 -> 6, 5 -> 1, 5 -> 2, 5 -> 3, 5 -> 4, 6 -> 1, 6 -> 5; the adjacencies 1-4, 1-5, 5-2, 5-3, 5-6 make the graph weakly connected, and the in-degree vector is d = (2, 1, 1, 2, 3, 3). Let g = (227, -991, -991, 329, 767, 659)/2694. The six coordinates of the transpose of M applied to M g - d vanish, so for every x the squared residual of x is the squared residual of g plus the squared norm of M (x - g); hence g minimizes the residual. A minimizer x then has M (x - g) = 0, and the six coordinate equations of this system force all coordinates of x - g to be equal; since the coordinates of g sum to 0, the squared norm of x exceeds that of g by six times the square of the common difference, so g has the least norm among the minimizers. The sum of g_j - g_i over the twelve arcs is -18/449, so the forward democracy coefficient of g is 1 + 18/(449 * 12) = 901/898 > 1.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("moutsinas-2021-democracy-coefficient-bound"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("hierarchy-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Leq(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula AllIn(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula AllOf(Formula variables, Formula body) =>
        Seq(Forall, Sp, variables, Comma, Sp, body);
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(F.Sum, Underscore, Grp(index), Sp, body);
    private static Formula Entry(Formula i, Formula j) => new Formula.Apply(F.Id("A"), [i, j]);
    private static Formula Coord(Formula vector, Formula i) => new Formula.Subscript(vector, i);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Vectors() => new Formula.Power(Reals(), F.Id("n"));
    private static Formula Residual(Formula x) => Call(F.Id("residual"), F.Id("A"), x);

    private static Formula IndegFormula()
    {
        Formula i = F.Id("i"), j = F.Id("j");
        return Disp(Equal(Call(F.Id("indeg"), F.Id("A"), j), SumOver(i, Entry(i, j))));
    }

    private static Formula LapFormula() =>
        Disp(Equal(Call(F.Id("lapT"), F.Id("A")),
            new Formula.Power(Parenthesized(new Formula.Binary(
                Call(F.Id("diag"), Call(F.Id("indeg"), F.Id("A"))), FormulaBinaryOperator.Subtract, F.Id("A"))),
                F.Id("T"))));

    private static Formula ResidualFormula()
    {
        Formula i = F.Id("i"), x = F.Id("x");
        Formula mx = Coord(Parenthesized(new Formula.Binary(Call(F.Id("lapT"), F.Id("A")),
            FormulaBinaryOperator.Multiply, x)), i);
        Formula diff = new Formula.Binary(mx, FormulaBinaryOperator.Subtract,
            Call(F.Id("indeg"), F.Id("A"), i));
        return Disp(Equal(Residual(x), SumOver(i, new Formula.Power(Parenthesized(diff), D(2)))));
    }

    private static Formula LevelsFormula()
    {
        Formula g = F.Id("g"), x = F.Id("x"), y = F.Id("y"), i = F.Id("i");
        Formula minimizes = AllIn(x, Vectors(), Leq(Residual(g), Residual(x)));
        Formula leastNorm = AllIn(x, Vectors(),
            Implies(AllIn(y, Vectors(), Leq(Residual(x), Residual(y))),
                Leq(SumOver(i, new Formula.Power(Coord(g, i), D(2))),
                    SumOver(i, new Formula.Power(Coord(x, i), D(2))))));
        return Disp(Iff(Call(F.Id("IsForwardLevels"), F.Id("A"), g), And(minimizes, leastNorm)));
    }

    private static Formula DemocracyFormula()
    {
        Formula g = F.Id("g"), i = F.Id("i"), j = F.Id("j");
        Formula num = SumOver(i, SumOver(j, new Formula.Binary(Entry(i, j), FormulaBinaryOperator.Multiply,
            Parenthesized(new Formula.Binary(Coord(g, j), FormulaBinaryOperator.Subtract, Coord(g, i))))));
        Formula den = SumOver(i, SumOver(j, Entry(i, j)));
        return Disp(Equal(Call(F.Id("forwardDemocracy"), F.Id("A"), g),
            new Formula.Binary(D(1), FormulaBinaryOperator.Subtract, new Formula.Fraction(num, den))));
    }

    private static Formula WeakFormula()
    {
        Formula i = F.Id("i"), j = F.Id("j");
        Formula rel = Seq(i, Comma, Sp, j, Sp, Mapsto, Sp,
            Rel(D(0), FormulaRelationOperator.LessThan, Entry(i, j)));
        return Disp(Iff(Call(F.Id("WeaklyConnected"), F.Id("A")),
            Call(F.Id("Connected"), Call(F.Id("fromRel"), rel))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), a = F.Id("A"), g = F.Id("g"), i = F.Id("i"), j = F.Id("j");
        Formula matrices = new Formula.Power(Reals(), Seq(n, Sp, Times, Sp, n));
        Formula nonneg = AllOf(Seq(i, Comma, Sp, j), Rel(D(0), FormulaRelationOperator.LessThanOrEqual, Entry(i, j)));
        Formula diag = AllOf(i, Equal(Entry(i, i), D(0)));
        Formula conclusion = AllIn(g, Vectors(),
            Implies(Call(F.Id("IsForwardLevels"), a, g),
                Leq(Call(F.Id("forwardDemocracy"), a, g), D(1))));
        Formula body = AllIn(n, Seq(Mathbb, Grp(F.Id("N"))), AllIn(a, matrices,
            Implies(nonneg, Implies(diag, Implies(Call(F.Id("WeaklyConnected"), a), conclusion)))));
        return Disp(Iff(F.Id("claim"), body));
    }
}

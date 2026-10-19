using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class HammingWeakTwoMetricDimensionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimension.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For 4 <= n < m < 2n - 2, the weak two-metric dimension of the rectangular "
            + "Hamming graph is min(ceil(2(n+m)/3), 2n - 2).",
        H("Rectangular weak two-metric dimension below the threshold"),
        Blocks(
            Paragraph(Text("The graph is the Cartesian product of complete graphs on "
                + "n and m vertices, with Hamming distance on its row and column coordinates. "
                + "A landmark set is weak two-resolving when the sum of absolute distance "
                + "differences is at least two for every distinct vertex pair. The "
                + "rectangular range below m = 2n - 2 is identified in Aryan Kumar, "
                + "arXiv:2609.32161v1, Section 7. Throughout the displayed statements, "
                + "natDiv(a,b) denotes natural number division; natDiv(2(n+m)+2,3) "
                + "equals ceil(2(n+m)/3).")),
            CountNode("left-count", "Generic left degree", "leftCount",
                "For arbitrary coordinate types with decidable equality, leftCount S a counts the edges of a finite incidence set S whose first coordinate is a.", DescribeRole.Definition),
            CountNode("right-count", "Generic right degree", "rightCount",
                "For arbitrary coordinate types with decidable equality, rightCount S b counts the edges of S whose second coordinate is b.", DescribeRole.Definition),
            CountNode("join", "Disjoint incidence union", "join",
                "For two finite incidence sets with separate coordinate types, join embeds both parts into disjoint sums and takes the union of their diagonal edge images.", DescribeRole.Definition),
            CountNode("join-disjoint", "Disjoint edge images", "join_disjoint",
                "For arbitrary finite incidence sets S,T, the left and right diagonal images used in join are disjoint because their first coordinates have different sum tags.", DescribeRole.Theorem),
            CountNode("join-card", "Cardinality of incidence union", "join_card",
                "For arbitrary finite incidence sets S,T, the cardinality of join S T is the sum of their cardinalities.", DescribeRole.Theorem),
            CountNode("join-left-inl", "Left degree in the first block", "join_left_inl",
                "At a left coordinate tagged inl a, the leftCount of join S T is exactly leftCount S a.", DescribeRole.Theorem),
            CountNode("join-left-inr", "Left degree in the second block", "join_left_inr",
                "At a left coordinate tagged inr a, the leftCount of join S T is exactly leftCount T a.", DescribeRole.Theorem),
            CountNode("join-right-inl", "Right degree in the first block", "join_right_inl",
                "At a right coordinate tagged inl b, the rightCount of join S T is exactly rightCount S b.", DescribeRole.Theorem),
            CountNode("join-right-inr", "Right degree in the second block", "join_right_inr",
                "At a right coordinate tagged inr b, the rightCount of join S T is exactly rightCount T b.", DescribeRole.Theorem),
            CountNode("left-count-map", "Left degree under relabeling", "leftCount_map",
                "For equivalences f,g of the coordinate types, mapping a finite incidence set through their product preserves its left degree at f a.", DescribeRole.Theorem),
            CountNode("right-count-map", "Right degree under relabeling", "rightCount_map",
                "For equivalences f,g of the coordinate types, mapping a finite incidence set through their product preserves its right degree at g b.", DescribeRole.Theorem),
            Node("ceiling-construction", "The two-thirds upper bound", "ceiling_upper",
                UpperFormula(true),
                "For every 4 <= n < m < 2n - 2, there is a weak two-resolving "
                    + "landmark set of cardinality at most ceil(2(n+m)/3). View "
                    + "landmarks as edges between row and column vertices. Remove "
                    + "one row and two columns when rows are no more numerous than "
                    + "columns, or two rows and one column otherwise, and place a "
                    + "two-edge star on the removed vertices. These reductions preserve "
                    + "positivity and the inequalities that each part has at most "
                    + "twice the size of the other. At a total of three to five "
                    + "vertices, explicit stars or paths complete the construction. "
                    + "Every vertex has positive degree and each edge has endpoint "
                    + "degree sum at least three, so the resulting set is weak "
                    + "two-resolving. Each three-vertex extension adds two edges.",
                DescribeRole.Theorem),
            Node("empty-row-construction", "The empty-row upper bound", "empty_row_upper",
                UpperFormula(false),
                "For every 4 <= n < m < 2n - 2, there is a weak two-resolving "
                    + "landmark set of cardinality at most 2n - 2. Leave row zero "
                    + "empty. In each row i from one to n - 1, place landmarks in "
                    + "columns 2(i-1) mod m and (2(i-1)+1) mod m. These columns are "
                    + "distinct, and the consecutive residues cover all columns "
                    + "because m <= 2(n-1). Every occupied row has degree two, "
                    + "every column has positive degree, and any disjoint landmarks "
                    + "have total endpoint degree at least six. The pair degree "
                    + "conditions therefore give weak two-resolution.", DescribeRole.Theorem),
            Node("rectangular-dimension-claim", "The exact rectangular formula", "claim",
                ClaimFormula(),
                "The formula asserts, for all natural n and m satisfying "
                    + "4 <= n < m < 2n - 2, equality of the weak two-metric dimension "
                    + "with the smaller of the two-thirds ceiling and 2n - 2.",
                DescribeRole.Definition),
            Node("rectangular-dimension-result", "Exact weak two-metric dimension", "result",
                Disp(new Formula.NamedConstant(FormulaIdentifier.Create("claim"))),
                "The formula holds throughout the stated rectangular range. "
                    + "The degree constraints give the minimum of the two quantities "
                    + "as a lower bound for every resolving set. The two constructions "
                    + "give each quantity as an upper bound, and hence give their "
                    + "minimum as the upper bound as well.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kumar-2026-rectangular-weak-two-metric-dimension"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock CountNode(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) =>
        new Formula.Relation(a, op, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(a, op, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Ceiling(Formula n, Formula m) =>
        Call("natDiv", Add(Mul(D(2), Add(n, m)), D(2)), D(3));
    private static Formula RowBound(Formula n) =>
        new Formula.Binary(Mul(D(2), n), FormulaBinaryOperator.Subtract, D(2));
    private static Formula Range(Formula n, Formula m, Formula body) =>
        Logic(Rel(D(4), FormulaRelationOperator.LessThanOrEqual, n), FormulaLogicOperator.Implies,
            Logic(Rel(n, FormulaRelationOperator.LessThan, m), FormulaLogicOperator.Implies,
                Logic(Rel(m, FormulaRelationOperator.LessThan, RowBound(n)),
                    FormulaLogicOperator.Implies, body)));

    private static Formula UpperFormula(bool ceiling)
    {
        var n = F.Id("n"); var m = F.Id("m"); var s = F.Id("S");
        var domain = Call("Finset", Call("Prod", Call("Fin", n), Call("Fin", m)));
        var existence = Exists("S", domain,
            Logic(Call("IsWeakResolving", D(2), s), FormulaLogicOperator.And,
                Rel(Call("card", s), FormulaRelationOperator.LessThanOrEqual,
                    ceiling ? Ceiling(n, m) : RowBound(n))));
        return Disp(All("n", Nat(), All("m", Nat(), Range(n, m, existence))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n"); var m = F.Id("m");
        var equality = Rel(Call("wdim", n, m, D(2)), FormulaRelationOperator.Equal,
            Call("min", Ceiling(n, m), RowBound(n)));
        return Disp(Logic(new Formula.NamedConstant(FormulaIdentifier.Create("claim")),
            FormulaLogicOperator.Iff,
            All("n", Nat(), All("m", Nat(), Range(n, m, equality)))));
    }
}

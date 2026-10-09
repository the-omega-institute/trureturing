using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class HammingWeakTwoMetricDimensionCoreDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weak two-resolving sets in a rectangular Hamming graph are governed by "
            + "their row degrees, column degrees, and the endpoint degrees of disjoint landmarks.",
        H("Separation and landmark degrees in rectangular Hamming graphs"),
        Blocks(
            Paragraph(Text("For natural numbers n and m, the vertices of the Cartesian "
                + "product of the complete graphs are Fin n times Fin m. The distance, "
                + "separation sum, and weak resolving property are those of Aryan Kumar, "
                + "arXiv:2609.32161v1, Section 1. The rectangular weak two-metric "
                + "dimension below m = 2n - 2 is the question in Section 7.")),
            Node("hamming-distance", "Hamming distance", "dist", DistanceFormula(),
                "For vertices x and y, the distance is the number of coordinates in "
                    + "which they differ: one indicator for the row and one for the column.",
                DescribeRole.Definition),
            Node("landmark-separation", "Separation sum", "delta", null,
                "For all natural n and m, a finite set S of vertices, and vertices x and y, "
                    + "delta S x y is the sum over every landmark w in S of the absolute "
                    + "difference between dist x w and dist y w. This absolute difference "
                    + "is Nat.dist, so the sum takes values in the natural numbers.",
                DescribeRole.Definition),
            Node("weak-resolving", "Weak resolving property", "IsWeakResolving",
                WeakFormula(),
                "A finite set S is weak k-resolving exactly when every two distinct "
                    + "vertices have separation at least the natural number k.",
                DescribeRole.Definition),
            Node("weak-dimension", "Weak metric dimension", "wdim", null,
                "For all natural n, m, and k, wdim n m k is the infimum in the natural "
                    + "numbers of the set of cardinalities of finite weak k-resolving "
                    + "sets in Fin n times Fin m. If this set of cardinalities is empty, "
                    + "the infimum is zero. For k equal to two, the entire vertex set "
                    + "is weak resolving, so the infimum is an attained minimum.",
                DescribeRole.Definition),
            Node("row-degree", "Row degree", "rowDegree", null,
                "For every finite set S of vertices and row i in Fin n, rowDegree S i "
                    + "is the cardinality of the landmarks whose first coordinate equals i.",
                DescribeRole.Definition),
            Node("column-degree", "Column degree", "colDegree", null,
                "For every finite set S of vertices and column j in Fin m, colDegree S j "
                    + "is the cardinality of the landmarks whose second coordinate equals j.",
                DescribeRole.Definition),
            Node("row-degree-sum", "Row degree sum", "sum_rowDegree", null,
                "For every finite landmark set S in Fin n times Fin m, the sum of "
                    + "rowDegree S i over all rows i equals the cardinality of S. "
                    + "Every landmark belongs to exactly one row.", DescribeRole.Theorem),
            Node("column-degree-sum", "Column degree sum", "sum_colDegree", null,
                "For every finite landmark set S in Fin n times Fin m, the sum of "
                    + "colDegree S j over all columns j equals the cardinality of S. "
                    + "Every landmark belongs to exactly one column.", DescribeRole.Theorem),
            Node("same-row-separation", "Separation in one row", "delta_same_row", null,
                "For every finite landmark set S, row i, and distinct columns j and j', "
                    + "delta S (i,j) (i,j') equals colDegree S j plus colDegree S j'. "
                    + "A landmark contributes one exactly when its column is one of "
                    + "the two columns, independently of its row.", DescribeRole.Theorem),
            Node("same-column-separation", "Separation in one column", "delta_same_col", null,
                "For every finite landmark set S, distinct rows i and i', and column j, "
                    + "delta S (i,j) (i',j) equals rowDegree S i plus rowDegree S i'. "
                    + "Only landmarks in these two rows contribute.", DescribeRole.Theorem),
            Node("rectangle-separation", "Separation across a rectangle", "delta_rectangle", null,
                "For every S, distinct rows i and i', and distinct columns j and j', "
                    + "delta S (i,j) (i',j') plus twice the membership indicator of "
                    + "(i,j') in S plus twice the membership indicator of (i',j) in S "
                    + "equals the sum of the two row degrees and the two column degrees. "
                    + "The crossed corners have equal distances to the compared vertices "
                    + "and therefore cancel two contributions each.", DescribeRole.Theorem),
            Node("resolving-row-pair", "Necessary row pair condition", "row_pair_degree", null,
                "For every weak two-resolving set S, distinct rows i and i', and "
                    + "any column j, rowDegree S i plus rowDegree S i' is at least "
                    + "two, by comparing the vertices (i,j) and (i',j).", DescribeRole.Theorem),
            Node("resolving-column-pair", "Necessary column pair condition", "col_pair_degree", null,
                "For every weak two-resolving set S, any row i, and distinct columns "
                    + "j and j', colDegree S j plus colDegree S j' is at least two, "
                    + "by comparing the vertices (i,j) and (i,j').", DescribeRole.Theorem),
            Node("disjoint-landmark-degrees", "Degree sum on disjoint landmarks",
                "disjoint_landmark_degree", null,
                "For every weak two-resolving set S and landmarks (i,j) and (i',j') "
                    + "in distinct rows and distinct columns, rowDegree S i plus "
                    + "colDegree S j plus rowDegree S i' plus colDegree S j' is at least "
                    + "six. Apply the rectangle identity to the crossed corners: "
                    + "the two landmarks subtract four from their degree sum.", DescribeRole.Theorem),
            Node("pair-degree-sufficiency", "Sufficient pair degree conditions",
                "weak_of_pair_degrees", null,
                "Let S be a finite landmark set. Suppose the degrees of every two "
                    + "distinct rows sum to at least two, the degrees of every two "
                    + "distinct columns sum to at least two, and the four endpoint "
                    + "degrees of every two landmarks in distinct rows and columns "
                    + "sum to at least six. Then S is weak two-resolving. For a "
                    + "rectangle with zero or one crossed landmark, the row and column "
                    + "conditions suffice; with two crossed landmarks, the endpoint "
                    + "condition supplies the remaining separation. Empty rows or "
                    + "columns are allowed whenever the pair conditions hold.", DescribeRole.Theorem),
            Node("positive-degree-sufficiency", "Sufficient positive degree conditions",
                "weak_of_degrees", null,
                "For every finite landmark set S, suppose every row and every column "
                    + "has degree at least one, and every landmark has the sum of its "
                    + "row and column degrees at least three. Then S is weak "
                    + "two-resolving. Positivity gives both pair conditions, and the "
                    + "two endpoint sums give at least six for disjoint landmarks.", DescribeRole.Theorem),
            Node("full-set-separation", "The full vertex set resolves", "univ_weak_two", null,
                "For every natural n and m, the entire set Fin n times Fin m is "
                    + "weak two-resolving. For distinct vertices x and y, the landmarks "
                    + "x and y each contribute dist x y, which is at least one. If "
                    + "there are no distinct vertices, the condition holds vacuously.", DescribeRole.Theorem),
            Node("dimension-upper-card", "A resolving set bounds the dimension", "wdim_le_card", null,
                "For every natural n, m, and k and finite weak k-resolving set S "
                    + "in Fin n times Fin m, wdim n m k is at most the cardinality "
                    + "of S, since that cardinality is among the achievable values.", DescribeRole.Theorem),
            Node("dimension-lower-card", "Uniform cardinality bounds the dimension", "le_wdim_two", null,
                "For every natural n, m, and a, if every finite weak two-resolving "
                    + "set in Fin n times Fin m has cardinality at least a, then "
                    + "wdim n m 2 is at least a. The full vertex set ensures that "
                    + "the set of achievable cardinalities is nonempty.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula? formula, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) =>
        new Formula.Relation(a, op, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(a, op, b);
    private static Formula Vertices(Formula n, Formula m) =>
        Call("Prod", Call("Fin", n), Call("Fin", m));
    private static Formula Indicator(Formula p) => Call("if", p, D(1), D(0));

    private static Formula DistanceFormula()
    {
        var n = F.Id("n"); var m = F.Id("m"); var x = F.Id("x"); var y = F.Id("y");
        var distance = new Formula.Binary(
            Indicator(Rel(Call("fst", x), FormulaRelationOperator.NotEqual, Call("fst", y))),
            FormulaBinaryOperator.Add,
            Indicator(Rel(Call("snd", x), FormulaRelationOperator.NotEqual, Call("snd", y))));
        return Disp(All("n", Nat(), All("m", Nat(), All("x", Vertices(n, m),
            All("y", Vertices(n, m), Rel(Call("dist", x, y),
                FormulaRelationOperator.Equal, distance))))));
    }

    private static Formula WeakFormula()
    {
        var n = F.Id("n"); var m = F.Id("m"); var k = F.Id("k");
        var s = F.Id("S"); var x = F.Id("x"); var y = F.Id("y");
        var condition = All("x", Vertices(n, m), All("y", Vertices(n, m),
            Logic(Rel(x, FormulaRelationOperator.NotEqual, y), FormulaLogicOperator.Implies,
                Rel(k, FormulaRelationOperator.LessThanOrEqual, Call("delta", s, x, y)))));
        return Disp(All("n", Nat(), All("m", Nat(), All("k", Nat(),
            All("S", Call("Finset", Vertices(n, m)),
                Logic(Call("IsWeakResolving", k, s), FormulaLogicOperator.Iff, condition))))));
    }
}

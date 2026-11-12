using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CommonNeighborhood;

internal sealed class NoncentralBoundDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/CommonNeighborhood/NoncentralBound.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/nath2021commutingcn");
    private static readonly LibraryNoteRef Supplier = LibraryNoteRef.Create("D5/L/FiniteGroups/jannat2024cnzagreb");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unrestricted finite nonabelian commuting-graph CN energy comparison.",
        H("Common-neighborhood energy of the noncentral commuting graph"), Blocks(
            Describe.Lean(DescribeId.Create("cn-noncentral-vertex"),
                DeclarationHandle.Create(Owner + "Vertex"), H("Individual noncentral vertices"),
                StatementSource.FromAuthor(VertexFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every group G, Vertex(G) is the subtype of elements outside its center. "
                    + "Vertices are individual elements. No quotient by conjugacy is taken."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cn-noncentral-graph"),
                DeclarationHandle.Create(Owner + "commutingGraph"), H("The exact simple graph"),
                StatementSource.FromAuthor(GraphFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The simple graph has the preceding vertex type; adjacency requires distinctness "
                    + "and equality of the two products in G. Its symmetry and absence of loops are part of the Lean definition. "
                    + "The value map is the canonical subtype inclusion into G."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cn-noncentral-result"),
                DeclarationHandle.Create(Owner + "result"), H("The full finite nonabelian bound"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(Source, Supplier),
                Blocks(
                    Paragraph(Text("For every group G with finite underlying set and a pair a,b whose products differ, "
                        + "the common-neighborhood energy of commutingGraph(G) is at most the displayed complete-graph benchmark. "
                        + "The cardinality is explicitly cast into the reals before subtracting one or two. "
                        + "No AC, quotient, order, regularity, genus or connectivity hypothesis is present.")),
                    Paragraph(Text("The existing generic graphEnergy(g,commonNeighbour), commonNeighbourMatrix, "
                        + "source_matrix_isHermitian and graphSpectrum in SubgroupGenerating.CyclicExtensionRefutation are reused. "
                        + "Their arbitrary finite simple graph parameter is instantiated by commutingGraph(G); the SGB graph "
                        + "and its source-specific theorems are unchanged. C has diagonal zero and off-diagonal common-neighbor "
                        + "cardinalities. graphSpectrum records every real Hermitian eigenvalue with multiplicity and graphEnergy "
                        + "sums their absolute values with zero centering in this matrix kind.")),
                    Paragraph(Text("Write A for adjacency, D for the degree diagonal, N for the group order, z for the center "
                        + "order and n=N-z. Entrywise counting gives C=A squared minus D. The general energy bound "
                        + "is twice the sum of degrees. In an orthogonal eigenbasis of C, the absolute difference of the two "
                        + "nonnegative diagonal quadratic terms is at most their sum. Summing gives the sum of their traces. "
                        + "This argument requires no simultaneous diagonalization of A and D.")),
                    Paragraph(Text("For each noncentral x, its centralizer K is proper. The subgroup index is at least two, "
                        + "so twice its order is at most N. The center, x, and all its graph neighbors are pairwise disjoint "
                        + "inside K; their cardinalities give degree(x)+z+1 at most the order of K. Hence twice degree(x) "
                        + "is at most n-z-2. Summation gives energy at most n(n-z-2). The difference from the target "
                        + "is (n-2) squared plus nz, which is nonnegative. All subtractions in this estimate occur in "
                        + "the integers or reals after finite cardinality relations have been justified.")),
                    Paragraph(Text("The complete-graph benchmark applies for n at least two. A noncentral centralizer "
                        + "contains the center and x, so the same index bound gives n at least z+2. "
                        + "The center contains the identity, whence z is at least one and n is at least three."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var parts = name.Split('.');
        Formula symbol = Seq(Operatorname, Grp(F.Id(parts[0])));
        for (var i = 1; i < parts.Length; i++)
            symbol = Seq(symbol, Dot, Seq(Operatorname, Grp(F.Id(parts[i]))));
        return args.Length == 0 ? symbol : new Formula.Apply(symbol, [.. args]);
    }
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, body);
    private static Formula GroupArguments(Formula body) =>
        All("G", Call("Type"), Instance(Call("Group", F.Id("G")), body));
    private static Formula Real(Formula a) => Seq(Open, a, Colon, Mathbb, Grp(F.Id("R")), Close);
    private static Formula Typed(Formula a, Formula type) => Seq(Open, a, Colon, type, Close);
    private static Formula Value(string name) => Call("Subtype.val", F.Id(name));

    private static Formula VertexFormula() => Disp(GroupArguments(Eq(
        Call("Vertex", F.Id("G")), Seq(OpenBrace, F.Id("x"), Colon, F.Id("G"), Mid,
            new Formula.Not(new Formula.Relation(F.Id("x"), FormulaRelationOperator.MemberOf,
                Call("Subgroup.center", F.Id("G")))), CloseBrace))));

    private static Formula GraphFormula() => Disp(GroupArguments(
        All("x", Call("Vertex", F.Id("G")), All("y", Call("Vertex", F.Id("G")),
            Iff(Call("SimpleGraph.Adj", Typed(Call("commutingGraph", F.Id("G")),
                    Call("SimpleGraph", Call("Vertex", F.Id("G")))), F.Id("x"), F.Id("y")),
                And(Ne(F.Id("x"), F.Id("y")),
                    Eq(Mul(Value("x"), Value("y")), Mul(Value("y"), Value("x")))))))));

    private static Formula ResultFormula()
    {
        var G = F.Id("G");
        var n = Real(Call("Fintype.card", Call("Vertex", G)));
        var nonabelian = Exists("a", G, Exists("b", G,
            Ne(Mul(F.Id("a"), F.Id("b")), Mul(F.Id("b"), F.Id("a")))));
        return Disp(GroupArguments(Instance(Call("Fintype", G), Imp(nonabelian,
            Le(Call("D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.graphEnergy",
                    Call("commutingGraph", G),
                    Call("D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.MatrixKind.commonNeighbour")),
                Mul(Mul(D(2), Sub(n, D(1))), Sub(n, D(2))))))));
    }
}

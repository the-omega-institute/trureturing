using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CommonNeighborhood;

internal sealed class NeighbourhoodCliqueBoundDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/CommonNeighborhood/NeighbourhoodCliqueBound.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/mazhang2026cncliques");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The neighbourhood-clique bound for the common-neighbourhood energy of every finite simple graph.",
        H("Neighbourhood-clique bound for common-neighbourhood energy"), Blocks(
            Describe.Lean(DescribeId.Create("cn-neighbourhood-clique-result"),
                DeclarationHandle.Create(Owner + "result"), H("The bound 4m - 2r"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every finite vertex type V and every simple graph g on V, the common-neighbourhood "
                        + "energy graphEnergy(g,commonNeighbour) is at most twice the sum over the vertices of max(d(v)-1,0), "
                        + "and that quantity equals 4m-2r, where m is the number of edges and r the number of vertices of "
                        + "positive degree. No connectivity or order hypothesis is present, so isolated vertices and the empty "
                        + "graph are covered because the lemma holds for every finite simple graph. This is Lemma 1 of Ma and "
                        + "Zhang, Zenodo DOI 10.5281/zenodo.24398996; the weaker bound 4m is due to Jannat, Nath and Das, "
                        + "Remark 4.7, as cited there.")),
                    Paragraph(Text("Let a_v be the indicator vector of the neighbourhood of v and d_v its size. Entrywise "
                        + "counting gives the common-neighbour matrix as A squared minus the degree diagonal, which is the sum "
                        + "over v of the outer product of a_v with itself minus the diagonal matrix of a_v. Put Pi_v for the "
                        + "outer product of a_v with itself divided by d_v, and zero when v is isolated. Then the summand for v "
                        + "is (d_v-1)Pi_v minus (diag a_v - Pi_v).")),
                    Paragraph(Text("The matrix (d_v-1)Pi_v is a nonnegative multiple of an outer product, hence positive "
                        + "semidefinite. The matrix diag a_v - Pi_v is symmetric and idempotent, because a_v has entries 0 and 1 "
                        + "and a_v has squared length d_v, hence positive semidefinite. Summing over v writes the "
                        + "common-neighbour matrix as P-Q with both parts positive semidefinite. The energy of such a difference "
                        + "is at most tr P + tr Q, the positive-semidefinite difference bound of the noncentral commuting-graph "
                        + "module. The Lean proof computes tr P + tr Q = 2 sum of max(d_v-1,0) directly; each trace equals half of it, "
                        + "a remark not separately formalized. The handshake identity, that the degrees sum to 2m, gives 4m-2r."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var parts = name.Split('.');
        Formula symbol = Seq(Operatorname, Grp(F.Id(parts[0])));
        for (var i = 1; i < parts.Length; i++)
            symbol = Seq(symbol, Dot, Seq(Operatorname, Grp(F.Id(parts[i]))));
        return args.Length == 0 ? symbol : new Formula.Apply(symbol, [.. args]);
    }
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Real(Formula a) => Seq(Open, a, Colon, Mathbb, Grp(F.Id("R")), Close);

    private static Formula ResultFormula()
    {
        var g = F.Id("g");
        var energy = Call("D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.graphEnergy", g,
            Call("D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.MatrixKind.commonNeighbour"));
        var degree = Real(Call("SimpleGraph.degree", g, F.Id("v")));
        var sum = Mul(D(2), Seq(new Formula.Subscript(Sum, Seq(F.Id("v"), Colon, Sp, F.Id("V"))), Sp,
            Call("max", Par(Sub(degree, D(1))), D(0))));
        var m = Real(Call("Finset.card", Call("SimpleGraph.edgeFinset", g)));
        var r = Real(Call("Finset.card", Seq(OpenBrace, F.Id("v"), Colon, F.Id("V"), Mid, Sp,
            Lt(D(0), Call("SimpleGraph.degree", g, F.Id("v"))), CloseBrace)));
        return Disp(And(Le(energy, sum), Eq(sum, Sub(Mul(D(4), m), Mul(D(2), r)))));
    }
}

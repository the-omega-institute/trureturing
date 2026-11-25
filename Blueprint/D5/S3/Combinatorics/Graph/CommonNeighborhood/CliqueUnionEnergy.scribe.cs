using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CommonNeighborhood;

internal sealed class CliqueUnionEnergyDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/CommonNeighborhood/CliqueUnionEnergy.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/mazhang2026cncliques");
    private static readonly LibraryNoteRef Definitions = LibraryNoteRef.Create("D5/L/FiniteGroups/nath2021commutingcn");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The common-neighbourhood energy of a disjoint union of cliques, its sharp complete-graph bound and the equality cases.",
        H("Common-neighbourhood energy of a union of cliques"), Blocks(
            Describe.Lean(DescribeId.Create("cn-clique-union-graph"),
                DeclarationHandle.Create(Owner + "cliqueUnion"), H("The disjoint union of cliques"),
                StatementSource.FromAuthor(GraphFormula()), AssessedProvenance.FromRepo(Source, Definitions),
                Blocks(Paragraph(Text("For a vertex type V and a labelling f from V to an arbitrary type, cliqueUnion(f) "
                    + "joins two distinct vertices exactly when they carry the same label. Its cliques are the fibres of f, "
                    + "and every disjoint union of complete graphs arises this way from the map sending a vertex to its "
                    + "component."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cn-clique-union-order"),
                DeclarationHandle.Create(Owner + "fibreCard"), H("Clique orders"),
                StatementSource.FromAuthor(OrderFormula()), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("fibreCard(f,i) is the number of vertices labelled i, so the clique orders s_i are "
                    + "the values of fibreCard(f,i) at the labels i in the image of f, and the number k of cliques is the "
                    + "cardinality of that image."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cn-clique-union-result"),
                DeclarationHandle.Create(Owner + "result"), H("Energy, bound and equality"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every finite vertex type V with n vertices and every labelling f, the "
                        + "common-neighbourhood energy of cliqueUnion(f) equals twice the sum of (s_i-1)(s_i-2) over the "
                        + "cliques. It is at most the complete-graph value 2(n-1)(n-2), and equality holds exactly when there "
                        + "is one clique, or two cliques that are both single vertices. The energy is graphEnergy(g,commonNeighbour) "
                        + "of the noncentral commuting-graph module, the sum of the absolute values of the real eigenvalues of "
                        + "the common-neighbour matrix with multiplicity. The statement needs no hypothesis k at least one: "
                        + "with V empty the energy is 0, the bound 2(0-1)(0-2)=4 is strict, and the right side of the equality "
                        + "criterion is false. This is Proposition 7 of Ma and Zhang, Zenodo DOI 10.5281/zenodo.24398996. Theorem 5.4 "
                        + "of Tak, Dutta and Nath, arXiv:2605.22160v1, states the strict inequality, which fails exactly for "
                        + "a single clique and for two isolated vertices; only the non-strict bound is attributable to it.")),
                    Paragraph(Text("Two distinct vertices of a clique of order s have s-2 common neighbours, and vertices of "
                        + "different cliques have none. Let Pi be the matrix with entry 1/s on pairs from one clique of order s "
                        + "and 0 otherwise. It is symmetric and idempotent, the orthogonal projection onto vectors constant on "
                        + "each clique. With the clique-constant weights W=(s-2)(s-1) and W'=max(s-2,0), the common-neighbour "
                        + "matrix equals P-Q for P=W Pi and Q=W'(1-Pi); the weight W' may replace s-2 because 1-Pi vanishes on "
                        + "cliques of order one. Both P and Q are positive semidefinite, as conjugates of nonnegative diagonal "
                        + "matrices by Pi and 1-Pi.")),
                    Paragraph(Text("The energy of P-Q is at most tr P + tr Q by the positive-semidefinite difference bound "
                        + "of the noncentral commuting-graph module. For the reverse inequality put S=2 Pi-1. Then 1+S=2 Pi and "
                        + "1-S=2(1-Pi) are positive semidefinite, so in an orthonormal eigenbasis of the common-neighbour matrix "
                        + "every diagonal entry of S lies in [-1,1], and tr(CS) is at most the sum of the absolute eigenvalues. "
                        + "Since P Pi=P and Q Pi=0, the product CS equals P+Q, so the energy is exactly tr P + tr Q. Each vertex "
                        + "of a clique of order s contributes 2(s-1)(s-2)/s, and summing over the s vertices of each clique "
                        + "gives the displayed formula.")),
                    Paragraph(Text("For the bound write g(s)=(s-1)(s-2) and let D be g(n) minus the sum of g(s_i). Adding a "
                        + "clique of order a to cliques of total order N changes D by g(a+N)-g(a)-g(N)=2aN-2. Induction gives "
                        + "D=2 with no clique, D=0 with one clique, and D at least (k-1)(k-2)+2(n-k) with k at least two cliques. "
                        + "Hence D is nonnegative; D=0 forces k at most two, and with k=2 it forces n=2, so both cliques are single "
                        + "vertices; conversely two single vertices give D=g(2)=0."))),
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
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Real(Formula a) => Seq(Open, a, Colon, Mathbb, Grp(F.Id("R")), Close);
    private static Formula Image() => Call("Finset.image", F.Id("f"), Call("Finset.univ"));

    private static Formula GraphFormula() => Disp(All("x", F.Id("V"), All("y", F.Id("V"),
        Iff(Call("SimpleGraph.Adj", Call("cliqueUnion", F.Id("f")), F.Id("x"), F.Id("y")),
            And(Ne(F.Id("x"), F.Id("y")),
                Eq(new Formula.Apply(F.Id("f"), [F.Id("x")]), new Formula.Apply(F.Id("f"), [F.Id("y")])))))));

    private static Formula OrderFormula() => Disp(All("i", Iota,
        Eq(Call("fibreCard", F.Id("f"), F.Id("i")),
            Call("Finset.card", Seq(OpenBrace, F.Id("x"), Colon, F.Id("V"), Mid, Sp,
                Eq(new Formula.Apply(F.Id("f"), [F.Id("x")]), F.Id("i")), CloseBrace)))));

    private static Formula ResultFormula()
    {
        var energy = Call("D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.graphEnergy",
            Call("cliqueUnion", F.Id("f")),
            Call("D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.MatrixKind.commonNeighbour"));
        var s = Real(Call("fibreCard", F.Id("f"), F.Id("i")));
        var n = Real(Call("Fintype.card", F.Id("V")));
        var sum = Seq(new Formula.Subscript(Sum, Mem(F.Id("i"), Image())), Sp,
            Par(Mul(Par(Sub(s, D(1))), Par(Sub(s, D(2))))));
        var bound = Mul(Mul(D(2), Par(Sub(n, D(1)))), Par(Sub(n, D(2))));
        var k = Call("Finset.card", Image());
        var equality = Or(Eq(k, D(1)), Par(And(Eq(k, D(2)),
            All("i", Mem(F.Id("i"), Image()), Eq(Call("fibreCard", F.Id("f"), F.Id("i")), D(1))))));
        return Disp(And(Eq(energy, Mul(D(2), sum)),
            And(Le(energy, bound), Par(Iff(Eq(energy, bound), Par(equality))))));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CommonNeighborhood;

internal sealed class RingNoncentralBoundDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/mazhang2026cncliques");
    private static readonly LibraryNoteRef Definitions = LibraryNoteRef.Create("D5/L/FiniteGroups/nath2021commutingcn");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The strict common-neighbourhood energy bound for the commuting graph of every finite noncommutative ring.",
        H("Common-neighbourhood energy of the noncentral commuting graph of a ring"), Blocks(
            Describe.Lean(DescribeId.Create("ring-cn-center"),
                DeclarationHandle.Create(Owner + "ringCenter"), H("The center"),
                StatementSource.FromAuthor(CenterFormula()), AssessedProvenance.FromRepo(Source, Definitions),
                Blocks(Paragraph(Text("ringCenter(R) is the set of elements commuting with every element of R. For an "
                    + "associative ring this is the usual center."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ring-cn-vertex"),
                DeclarationHandle.Create(Owner + "Vertex"), H("Individual noncentral vertices"),
                StatementSource.FromAuthor(VertexFormula()), AssessedProvenance.FromRepo(Source, Definitions),
                Blocks(Paragraph(Text("Vertex(R) is the subtype of elements outside the center; vertices are individual "
                    + "elements."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ring-cn-graph"),
                DeclarationHandle.Create(Owner + "commutingGraph"), H("The commuting graph"),
                StatementSource.FromAuthor(GraphFormula()), AssessedProvenance.FromRepo(Source, Definitions),
                Blocks(Paragraph(Text("Two distinct noncentral elements are adjacent exactly when their two products in R "
                    + "are equal."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ring-cn-result"),
                DeclarationHandle.Create(Owner + "result"), H("The strict bound"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every finite associative ring R, not assumed unital and with no "
                        + "commutative-centralizer hypothesis, that has two elements whose products differ, write z for the "
                        + "order of the center and n for the number of noncentral elements. Then z is at least 1, n is at least "
                        + "z+2, hence at least 3, and the common-neighbourhood energy of commutingGraph(R) is at most "
                        + "n max(n-z-4,0), which is at most n(n-z-2), which is strictly below the complete-graph value "
                        + "2(n-1)(n-2). The bound n(n-z-2) < 2(n-1)(n-2) is Corollary 3 of Ma and Zhang, Zenodo DOI "
                        + "10.5281/zenodo.24398996; the factor max(n-z-4,0) sharpens it through the neighbourhood-clique "
                        + "bound.")),
                    Paragraph(Text("For a noncentral x, the elements commuting with x form an additive subgroup, because "
                        + "multiplication distributes over addition and negation. It is proper since x is noncentral, so its "
                        + "index is at least two and it has at most half of the elements of R. It contains the center, x itself "
                        + "and every graph neighbour of x, and these three parts are disjoint. Hence deg(x)+z+1 is at most |R|/2, "
                        + "that is 2deg(x) is at most n-z-2.")),
                    Paragraph(Text("The center contains 0, so z is at least 1, and one noncentral element gives n at least z+2. "
                        + "The neighbourhood-clique bound gives an energy at most twice the sum of max(deg(v)-1,0), and each "
                        + "summand is at most max(n-z-4,0)/2. Finally 2(n-1)(n-2)-n(n-z-2) = (n-2)^2+nz is positive."))),
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
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Real(Formula a) => Seq(Open, a, Colon, Mathbb, Grp(F.Id("R")), Close);
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, body);

    private static Formula CenterFormula() => Disp(Eq(Call("ringCenter", F.Id("R")),
        Seq(OpenBrace, F.Id("x"), Mid, Sp, All("y", F.Id("R"),
            Eq(Mul(F.Id("x"), F.Id("y")), Mul(F.Id("y"), F.Id("x")))), CloseBrace)));

    private static Formula VertexFormula() => Disp(Eq(Call("Vertex", F.Id("R")),
        Seq(OpenBrace, F.Id("x"), Colon, F.Id("R"), Mid, Sp,
            new Formula.Not(new Formula.Relation(F.Id("x"), FormulaRelationOperator.MemberOf,
                Call("ringCenter", F.Id("R")))), CloseBrace)));

    private static Formula GraphFormula() => Disp(All("x", Call("Vertex", F.Id("R")), All("y", Call("Vertex", F.Id("R")),
        Iff(Call("SimpleGraph.Adj", Call("commutingGraph", F.Id("R")), F.Id("x"), F.Id("y")),
            And(Ne(F.Id("x"), F.Id("y")), Eq(Mul(F.Id("x"), F.Id("y")), Mul(F.Id("y"), F.Id("x"))))))));

    private static Formula ResultFormula()
    {
        var R = F.Id("R");
        var z = Call("Fintype.card", Call("ringCenter", R));
        var n = Call("Fintype.card", Call("Vertex", R));
        var nr = Real(n);
        var zr = Real(z);
        var energy = Call("D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.graphEnergy",
            Call("commutingGraph", R),
            Call("D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.MatrixKind.commonNeighbour"));
        var sharp = Mul(nr, Call("max", Sub(Sub(nr, zr), D(4)), D(0)));
        var weak = Mul(nr, Par(Sub(Sub(nr, zr), D(2))));
        var bench = Mul(Mul(D(2), Par(Sub(nr, D(1)))), Par(Sub(nr, D(2))));
        var noncommutative = Exists("a", R, Exists("b", R, Ne(Mul(F.Id("a"), F.Id("b")), Mul(F.Id("b"), F.Id("a")))));
        var body = And(Le(D(1), z), And(Le(Add(z, D(2)), n), And(Le(D(3), n),
            And(Le(energy, sharp), And(Le(sharp, weak), Lt(weak, bench))))));
        return Disp(All("R", Call("Type"), Instance(Call("NonUnitalRing", R), Instance(Call("Fintype", R),
            Imp(noncommutative, body)))));
    }
}

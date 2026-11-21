using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CommonNeighborhood;

internal sealed class RingNoncentralBoundDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/CommonNeighborhood/RingNoncentralBound.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/mazhang2026cncliques");
    
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The strict common-neighbourhood energy bound for the commuting graph of every finite noncommutative ring.",
        H("Common-neighbourhood energy of the noncentral commuting graph of a ring"), Blocks(
            Describe.Lean(DescribeId.Create("ring-cn-center"),
                DeclarationHandle.Create(Owner + "ringCenter"), H("The center"),
                StatementSource.FromAuthor(CenterFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("ringCenter(R) is the centralizer of the whole ring, the set of elements commuting with "
                    + "every element of R. For an associative ring this is the usual center; in general it is the commutative center."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ring-cn-vertex"),
                DeclarationHandle.Create(Owner + "Vertex"), H("Individual noncentral vertices"),
                StatementSource.FromAuthor(VertexFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Vertex(R) is the subtype of elements outside the center; vertices are individual "
                    + "elements."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ring-cn-graph"),
                DeclarationHandle.Create(Owner + "commutingGraph"), H("The commuting graph"),
                StatementSource.FromAuthor(GraphFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Two distinct noncentral elements are adjacent exactly when their two products in R "
                    + "are equal."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ring-cn-centralizer-card"),
                DeclarationHandle.Create(Owner + "centralizerCard"), H("Centralizer orders"),
                StatementSource.FromAuthor(CentralizerFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("centralizerCard(R,x) is the number of elements commuting with x."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ring-cn-result"),
                DeclarationHandle.Create(Owner + "result"), H("The strict bound"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Let R be a finite ring whose multiplication distributes over addition, associative or "
                        + "not and not necessarily unital, with two elements whose products differ. Write z for the order of "
                        + "its center, n for the number of noncentral elements, C(x) for the centralizer of x and p for the "
                        + "least prime dividing |R|. Then z is at least 1, n is at least 3z, n is at least z+2 and at least 3, "
                        + "and z divides n. The common-neighbourhood energy of commutingGraph(R) is at most twice the sum over "
                        + "noncentral x of max(|C(x)|-z-2,0); that sum is at most n max(2(n+z)/p-2z-4,0), which is at most "
                        + "n max(n-z-4,0), which is at most n(n-z-2), which is strictly below the complete-graph value "
                        + "2(n-1)(n-2). For associative rings, n at least z+2 and the bound n(n-z-2) < 2(n-1)(n-2) are "
                        + "Corollary 3, and the per-vertex sum and the least-prime-divisor form are Corollary 4, of Ma and "
                        + "Zhang, Zenodo DOI 10.5281/zenodo.24398996; the repository drops associativity and adds n at least "
                        + "3z and z dividing n.")),
                    Paragraph(Text("For a noncentral x, the elements commuting with x form an additive subgroup, because "
                        + "multiplication distributes over addition and negation. It is exactly the disjoint union of the "
                        + "center, x itself and the graph neighbours of x, so deg(x) = |C(x)|-z-1. It is proper since x is "
                        + "noncentral, so its index is a divisor of |R| exceeding one, hence at least p, and p|C(x)| is at most "
                        + "|R| = n+z. The center is itself an additive subgroup, properly contained in C(x) because x lies in "
                        + "C(x); by Lagrange |C(x)| is at least 2z and |R| at least 4z, so n is at least 3z, and z divides "
                        + "|R| and hence n.")),
                    Paragraph(Text("The neighbourhood-clique bound gives an energy at most twice the sum of max(deg(x)-1,0), "
                        + "which is the displayed per-vertex sum. Each summand is at most max((n+z)/p-z-2,0), and p is at "
                        + "least 2. Finally 2(n-1)(n-2)-n(n-z-2) = (n-2)^2+nz is positive.")),
                    Paragraph(Text("The hypotheses are needed as follows. Without two non-commuting elements the vertex type "
                        + "is empty and n is at least z+2 fails. Finiteness is needed for the orders and the spectrum. "
                        + "Additive inverses are needed for the centralizer to be an additive subgroup to which Lagrange's "
                        + "theorem applies; in a semiring the centralizer is only an additive submonoid. That last remark is "
                        + "not separately formalized. The four-element ring with a^2=a, ab=b, ba=0, b^2=0 has z=1, n=3 and no "
                        + "edges, so the energy equals the bound n max(n-z-4,0)=0; this example is not compiled."))),
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

    private static Formula CentralizerFormula() => Disp(All("x", F.Id("R"),
        Eq(Call("centralizerCard", F.Id("R"), F.Id("x")),
            Call("Fintype.card", Seq(OpenBrace, F.Id("y"), Colon, F.Id("R"), Mid, Sp,
                Eq(Mul(F.Id("x"), F.Id("y")), Mul(F.Id("y"), F.Id("x"))), CloseBrace)))));

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
        var c = Real(Call("centralizerCard", R, Call("Subtype.val", F.Id("x"))));
        var p = Real(Call("Nat.minFac", Call("Fintype.card", R)));
        var perVertex = Mul(D(2), Seq(new Formula.Subscript(Sum, Seq(F.Id("x"), Colon, Sp, Call("Vertex", R))), Sp,
            Call("max", Sub(Sub(c, zr), D(2)), D(0))));
        var prime = Mul(nr, Call("max", Sub(Sub(new Formula.Fraction(Mul(D(2), Par(Add(nr, zr))), p), Mul(D(2), zr)), D(4)), D(0)));
        var sharp = Mul(nr, Call("max", Sub(Sub(nr, zr), D(4)), D(0)));
        var weak = Mul(nr, Par(Sub(Sub(nr, zr), D(2))));
        var bench = Mul(Mul(D(2), Par(Sub(nr, D(1)))), Par(Sub(nr, D(2))));
        var noncommutative = Exists("a", R, Exists("b", R, Ne(Mul(F.Id("a"), F.Id("b")), Mul(F.Id("b"), F.Id("a")))));
        var orders = And(Le(D(1), z), And(Le(Mul(D(3), z), n), And(Le(Add(z, D(2)), n), And(Le(D(3), n),
            new Formula.Relation(z, FormulaRelationOperator.Divides, n)))));
        var chain = And(Le(energy, perVertex), And(Le(perVertex, prime), And(Le(prime, sharp),
            And(Le(sharp, weak), Lt(weak, bench)))));
        var body = And(orders, chain);
        return Disp(All("R", Call("Type"), Instance(Call("NonUnitalNonAssocRing", R), Instance(Call("Fintype", R),
            Imp(noncommutative, body)))));
    }
}

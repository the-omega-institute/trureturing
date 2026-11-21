using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CommonNeighborhood;

internal sealed class GroupCentralizerBoundDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/CommonNeighborhood/GroupCentralizerBound.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/mazhang2026cncliques");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Centralizer and least-prime common-neighbourhood energy bounds for the commuting graph of every finite nonabelian group.",
        H("Centralizer bounds for the commuting graph of a finite group"), Blocks(
            Describe.Lean(DescribeId.Create("group-cn-centralizer-result"),
                DeclarationHandle.Create(Owner + "result"), H("Centralizer and least-prime bounds"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every finite group G with two elements whose products differ, write z for the order of "
                        + "its center, n for the number of noncentral elements, C(x) for the centralizer of x and p for the least "
                        + "prime dividing |G|. Then z is at least 1, n is at least (p^2-1)z, n is at least z+2 and at least 3, and z "
                        + "divides n. The common-neighbourhood energy of the commuting graph on the individual noncentral elements "
                        + "(commutingGraph(G) of the noncentral commuting-graph module) is at most twice the sum over noncentral x "
                        + "of max(|C(x)|-z-2,0), and that is at most n max(2(n+z)/p-2z-4,0). This last quantity is at most "
                        + "2n((n+z)/p-z-1), and also at most n max(n-z-4,0), which is at most n(n-z-2), strictly below the "
                        + "complete-graph value 2(n-1)(n-2).")),
                    Paragraph(Text("The per-vertex sum and the bound 2n((n+z)/p-z-1) are Corollary 4 of Ma and Zhang, Zenodo DOI "
                        + "10.5281/zenodo.24398996, and the strict bound n(n-z-2) < 2(n-1)(n-2) with n at least z+2 at least 3 is "
                        + "their Theorem 2. The repository sharpens the least-prime form to n max(2(n+z)/p-2z-4,0) and adds n at "
                        + "least (p^2-1)z and z dividing n. The ring analogue is RingNoncentralBound.")),
                    Paragraph(Text("For a noncentral x, the center, x itself and the graph neighbours of x are disjoint inside "
                        + "the centralizer C(x), so deg(x)+z+1 is at most |C(x)|; this inequality is the noncentral "
                        + "commuting-graph module's degree_and_center_le_centralizer. C(x) is a proper subgroup, so its index is a "
                        + "divisor of |G| exceeding one, hence at least p, and p|C(x)| is at most |G| = n+z. The center is a proper "
                        + "subgroup of C(x) whose index is likewise at least p, so p^2 z is at most |G| and n is at least "
                        + "(p^2-1)z; Lagrange also gives z dividing |G| and hence n. The neighbourhood-clique bound and the degree "
                        + "inequality give the per-vertex energy bound; the remaining steps use p at least 2 and |C(x)| at least "
                        + "z+1, and 2(n-1)(n-2)-n(n-z-2) = (n-2)^2+nz is positive.")),
                    Paragraph(Text("The hypotheses are needed as follows. Without two non-commuting elements the vertex type is "
                        + "empty and n at least z+2 fails. Finiteness is needed for the orders and the spectrum. The quaternion "
                        + "group and the extraspecial groups of order p^3 attain p^2 z = |G|; in the symmetric group on three "
                        + "letters and the quaternion group the least-prime bound is 0, which equals the energy. These examples "
                        + "are not compiled."))),
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
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula Real(Formula a) => Seq(Open, a, Colon, Mathbb, Grp(F.Id("R")), Close);
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, body);

    private static Formula ResultFormula()
    {
        var G = F.Id("G");
        var vertex = Call("D5.S3.Combinatorics.Graph.CommonNeighborhood.NoncentralBound.Vertex", G);
        var graph = Call("D5.S3.Combinatorics.Graph.CommonNeighborhood.NoncentralBound.commutingGraph", G);
        var z = Call("Fintype.card", Call("Subgroup.center", G));
        var n = Call("Fintype.card", vertex);
        var nr = Real(n);
        var zr = Real(z);
        var energy = Call("D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.graphEnergy", graph,
            Call("D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation.MatrixKind.commonNeighbour"));
        var c = Real(Call("Fintype.card", Call("Subgroup.centralizer", Seq(OpenBrace, Call("Subtype.val", F.Id("x")), CloseBrace))));
        var p = Real(Call("Nat.minFac", Call("Fintype.card", G)));
        var perVertex = Mul(D(2), Seq(new Formula.Subscript(Sum, Seq(F.Id("x"), Colon, Sp, vertex)), Sp,
            Call("max", Sub(Sub(c, zr), D(2)), D(0))));
        var ratio = new Formula.Fraction(Add(nr, zr), p);
        var prime = Mul(nr, Call("max", Sub(Sub(new Formula.Fraction(Mul(D(2), Par(Add(nr, zr))), p), Mul(D(2), zr)), D(4)), D(0)));
        var paper = Mul(Mul(D(2), nr), Par(Sub(Sub(ratio, zr), D(1))));
        var sharp = Mul(nr, Call("max", Sub(Sub(nr, zr), D(4)), D(0)));
        var weak = Mul(nr, Par(Sub(Sub(nr, zr), D(2))));
        var bench = Mul(Mul(D(2), Par(Sub(nr, D(1)))), Par(Sub(nr, D(2))));
        var nonabelian = Exists("a", G, Exists("b", G, Ne(Mul(F.Id("a"), F.Id("b")), Mul(F.Id("b"), F.Id("a")))));
        var p2 = Sub(new Formula.Power(Call("Nat.minFac", Call("Fintype.card", G)), D(2)), D(1));
        var orders = And(Le(D(1), z), And(Le(Mul(Par(p2), z), n), And(Le(Add(z, D(2)), n), And(Le(D(3), n),
            new Formula.Relation(z, FormulaRelationOperator.Divides, n)))));
        var chain = And(Le(energy, perVertex), And(Le(perVertex, prime), And(Le(prime, paper),
            And(Le(prime, sharp), And(Le(sharp, weak), Lt(weak, bench))))));
        return Disp(All("G", Call("Type"), Instance(Call("Group", G), Instance(Call("Fintype", G),
            Imp(nonabelian, And(orders, chain))))));
    }
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Kozlov;

internal sealed class PositiveGapPerronRatioDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Kozlov/PositiveGapPerronRatio.";
    private static readonly LibraryNoteRef Snellman = LibraryNoteRef.Create("D5/L/Convexity/snellman2026kozlov");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At every positive integer gap and for every ground-set size at least four, the full proper transfer and the lattice transfer have positive complex spectral radii. The proper radius divided by the lattice radius is less than one.",
        H("The positive-gap Kozlov Perron-root ratio"),
        Blocks(
            Describe.Lean(DescribeId.Create("kozlov-positive-gap-condition"),
                DeclarationHandle.Create(Prefix + "positiveGapCondition"), H("The gap test"),
                StatementSource.FromAuthor(GapTest()), AssessedProvenance.FromLiterature(Snellman),
                Blocks(Paragraph(Text("An index i of Fin(n) represents predecessor top degree i.val + 1. The first deficiency of the incoming vector f is indeg(f). The positive gap test is the strict inequality in equation (42) of Part III."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kozlov-positive-gap-proper-transfer"),
                DeclarationHandle.Create(Prefix + "properPositiveGapTransfer"), H("The full proper transfer"),
                StatementSource.FromAuthor(Transfer("P", "ProperStates", "S")), AssessedProvenance.FromLiterature(Snellman),
                Blocks(Paragraph(Text("The state set ProperStates(n) is the ordered list −1, 0, 1, …, n. S(n) is the set of distinct f-vectors of downsets on n vertices containing the empty face and all singletons. In count(X,a,b,d), row a is the predecessor top and column b is the incoming top. This is the cardinality of vectors f in X with top(f) = b and a < indeg(f) + d. The proper count is the transfer of Part II, Definition 28 and Theorem 41, after retaining just the proper vectors."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kozlov-positive-gap-lattice-transfer"),
                DeclarationHandle.Create(Prefix + "latticePositiveGapTransfer"), H("The lattice transfer"),
                StatementSource.FromAuthor(Transfer("L", "LatticeStates", "Lattice")), AssessedProvenance.FromLiterature(Snellman),
                Blocks(Paragraph(Text("LatticeStates(n) consists of the positive degrees 1, …, n, represented by Fin(n). Lattice(n) consists of the integer vectors in the real convex hull of S(n). The transfer counts incoming vectors as in equation (42) and Corollary 33 of Part III."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kozlov-positive-gap-perron-root-ratio"),
                DeclarationHandle.Create(Prefix + "positive_gap_perron_root_ratio"), H("Strict comparison of the complex spectral radii"),
                StatementSource.FromAuthor(Ratio()), AssessedProvenance.FromRepo(Snellman),
                Blocks(
                    Paragraph(Text("P and L are the counted transfers defined above. The radii are taken after casting every natural entry to the complex numbers. The function toReal reads the finite radius as a real number. The lattice radius is positive as a real denominator.")),
                    Paragraph(Text("Complete skeletons supply consecutive transitions and loops in both positive-degree supports. In the full proper matrix the two columns of degrees −1 and 0 vanish, so adjoining these states adds only zero roots to the characteristic polynomial.")),
                    Paragraph(Text("The lattice vector (1,n,2,1,0,…) has top three and first deficiency two. A three-element face would force at least three two-element faces, so this vector increases the lattice count in row one and column three. Pairing the matrix difference with a positive right vector of the proper block and a positive left vector of the lattice matrix gives a strictly positive sum."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula EqTo(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula OverSizeAndGap(Formula body) => All("n", Nat(), All("d", Nat(), body));

    private static Formula GapTest()
    {
        var n = F.Id("n");
        var d = F.Id("d");
        var i = F.Id("i");
        var f = F.Id("f");
        var test = new Formula.Logic(Call("positiveGapCondition", d, i, f), FormulaLogicOperator.Iff,
            Less(Add(Call("val", i), D(1)), Add(Call("indeg", f), d)));
        return Disp(OverSizeAndGap(All("i", Call("Fin", n), All("f", Call("FVector", n), test))));
    }

    private static Formula Transfer(string transfer, string states, string carrier)
    {
        var n = F.Id("n");
        var d = F.Id("d");
        var a = F.Id("a");
        var b = F.Id("b");
        var entries = Call("count", Call(carrier, n), a, b, d);
        return Disp(OverSizeAndGap(All("a", Call(states, n), All("b", Call(states, n),
            EqTo(Call(transfer, n, d, a, b), entries)))));
    }

    private static Formula Ratio()
    {
        var n = F.Id("n");
        var d = F.Id("d");
        var p = Call("radius", Call("complex", Call("P", n, d)));
        var l = Call("radius", Call("complex", Call("L", n, d)));
        var ratio = new Formula.Fraction(Call("toReal", p), Call("toReal", l));
        var denominator = Less(D(0), Call("toReal", l));
        var comparison = And(Less(D(0), p), And(Less(D(0), l), And(Less(p, l),
            And(denominator, Less(ratio, D(1))))));
        return Disp(OverSizeAndGap(Implies(And(Le(D(4), n), Le(D(1), d)), comparison)));
    }
}

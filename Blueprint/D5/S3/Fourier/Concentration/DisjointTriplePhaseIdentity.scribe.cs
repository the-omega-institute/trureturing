using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class DisjointTriplePhaseIdentityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/DisjointTriplePhaseIdentity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One mixed phase term completes the disjoint triple sum for complementary weights.",
        H("The mixed phase term in the disjoint triple sum"),
        Blocks(Describe.Lean(
            DescribeId.Create("disjoint-triple-phase-identity"),
            DeclarationHandle.Create(Owner + ".disjoint_triple_phase_identity"),
            H("Pair contribution and mixed phase term"),
            StatementSource.FromAuthor(DisplayIdentity()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let J be finite with n elements, and let x and y take values in a "
                    + "commutative ring. Assume x(j)y(j)=1 for every j. Write X and Y "
                    + "for the sums of x and y, and X₂ and Y₂ for the sums of their squares. "
                    + "The quantity D sums products over ordered pairs of ordered triples "
                    + "with no index shared between the two sides. The triples may repeat indices.")),
                Paragraph(Text(
                    "Inclusion and exclusion uses the nine possible equalities between "
                    + "left and right positions. Each subset of equalities partitions the "
                    + "six positions into connected components, and each component has one "
                    + "freely chosen index. A component with a left positions and b right "
                    + "positions contributes the sum of x(j) to the power a times y(j) "
                    + "to the power b. Complementarity cancels the matched powers.")),
                Paragraph(Text(
                    "The two types of three-edge star with imbalance of magnitude two have three "
                    + "choices of center on the opposite side and sign minus. They give "
                    + "the terms X₂Y² and Y₂X². The other component profiles yield the "
                    + "polynomial in n and XY.")),
                Paragraph(Text(
                    "For unit-weight integer frequencies g, take x(j) and y(j) to be "
                    + "Laurent monomials at exponents g(j) and −g(j). The two extra terms "
                    + "have exponents 2g(i)−g(j)−g(k) and their negatives. Extracting a "
                    + "band selects the corresponding signed frequency differences."))),
            DescribeRole.Theorem))));

    private static Formula DisplayIdentity()
    {
        var n = F.Id("n");
        var u = F.Id("u");
        var x = F.Id("X");
        var y = F.Id("Y");
        var j = F.Id("j");
        var alphabet = F.Id("J");
        var ring = F.Id("R");
        var left = F.Id("x");
        var right = F.Id("y");
        var x2 = new Formula.Subscript(x, D(2));
        var y2 = new Formula.Subscript(y, D(2));
        var sum = Seq(Sum, Underscore, Grp(j, Sp, InMacro, Sp, alphabet));
        var xj = Call("x", j);
        var yj = Call("y", j);
        var pair = new Formula.Subscript(F.Id("P"), n);
        return Disp(new Formula.Aligned([
            Seq(Amp, Forall, Sp, alphabet, Quad, OpenBracket, Call("Fintype", alphabet), CloseBracket,
                Quad, OpenBracket, Call("DecidableEq", alphabet), CloseBracket,
                Quad, Forall, Sp, ring, Quad, OpenBracket, Call("CommRing", ring), CloseBracket, Comma),
            Seq(Amp, Forall, Sp, left, Comma, right, Colon, alphabet, To, Sp, ring, Comma, Quad,
                Open, Forall, Sp, j, InMacro, Sp, alphabet, Comma, xj, yj, Eq, D(1), Close, Implies),
            Seq(Amp, n, Eq, Bar, alphabet, Bar, Comma, Quad, Sp, x, Eq, sum, xj, Comma,
                Quad, Sp, y, Eq, sum, yj, Comma, Quad, Sp, x2, Eq, sum, Pow(xj, 2),
                Comma, Quad, Sp, y2, Eq, sum, Pow(yj, 2), Comma),
            Seq(Amp, Call("D", left, right), Sp, Eq, Sp,
                new Formula.Apply(pair, [Seq(x, y)]), Sp, Minus, Sp, D(3), Open,
                x2, Pow(y, 2), Sp, Plus, Sp, y2, Pow(x, 2), Close, Comma),
            Seq(Amp, Forall, Sp, u, Colon, ring, Comma, Quad, new Formula.Apply(pair, [u]),
                Sp, Eq, Sp, Pow(u, 3), Sp, Plus, Sp,
                Open, D(1, 8), Sp, Minus, Sp, D(9), n, Close, Pow(u, 2), Sp, Plus, Sp,
                Open, D(1, 8), Pow(n, 2), Sp, Minus, Sp, D(6, 3), n, Sp, Plus, Sp,
                D(5, 1), Close, u),
            Seq(Amp, Quad, Minus, Sp, D(6), Pow(n, 3), Sp, Plus, Sp, D(2, 7),
                Pow(n, 2), Sp, Minus, Sp, D(3, 1), n, Dot)
        ]));
    }

    private static Formula Pow(Formula value, byte exponent) => new Formula.Power(value, D(exponent));
}

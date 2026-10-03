using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Mordell;

internal sealed class GoldenCubicBlockMordellTwistsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/Mordell/GoldenCubicBlockMordellTwists.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive golden cubic-block layer gives two elliptic cubic twists and explicit "
            + "integral points of infinite order, with the same property on unfactored models.",
        H("Two Non-Torsion Cubic Twists on Every Golden Block Layer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-cubic-block"),
                DeclarationHandle.Create(Prefix + "block"),
                H("The actual cubic block"),
                StatementSource.FromAuthor(Disp(Seq(
                    Sub("B", "j"), Sp, Eq, Sp,
                    new Formula.Power(Sub("L", new Formula.Power(D(3), F.Id("j"))), D(2)),
                    Sp, Plus, Sp, D(3)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each natural layer j, the positive actual block is the square of "
                    + "the Lucas number at index 3^j, plus three."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("canonical-cube-part-root"),
                DeclarationHandle.Create(Prefix + "cubePartRoot"),
                H("The canonical cube-part root"),
                StatementSource.FromAuthor(Disp(Seq(
                    Sub("c", "j"), Sp, Eq, Sp,
                    Call("floorRoot", D(3), Sub("B", "j"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Pinned Nat.floorRoot is factorization-based. Its exponent at prime p is "
                    + "floor(v_p(B_j)/3), so its cube divides the block; it is not the "
                    + "ordinary numerical cube-root floor."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("canonical-cubefree-part"),
                DeclarationHandle.Create(Prefix + "cubefreePart"),
                H("The canonical cubefree factor"),
                StatementSource.FromAuthor(Disp(Seq(
                    Sub("d", "j"), Sp, Eq, Sp,
                    new Formula.Fraction(Sub("B", "j"),
                        new Formula.Power(Sub("c", "j"), D(3)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The quotient is integral and B_j=d_j*c_j^3. Every prime exponent "
                    + "of d_j is the corresponding exponent of B_j modulo three."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("integral-infinite-order-mordell-point"),
                DeclarationHandle.Create(Prefix + "InfiniteOrderPoint"),
                H("An integral nonsingular Mordell point of infinite order"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("InfiniteOrderPoint", F.Id("b"), F.Id("X"), F.Id("Y")), Sp, Iff, Sp,
                    Call("NonsingularPoint", F.Id("b"), F.Id("X"), F.Id("Y")), Sp,
                    Land, Sp, Neg, Call("IsOfFinAddOrder", F.Id("X"), F.Id("Y"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The integral coordinates are cast to rational coordinates on the "
                    + "nonsingular affine locus of Y^2=X^3+b. The resulting group point "
                    + "does not have finite additive order."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("two-cubic-twists-on-every-actual-layer"),
                DeclarationHandle.Create(Prefix + "actual_cubic_twists"),
                H("Two twists on every actual layer"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For j>=1, all four models are elliptic: E^-_j has coefficient -3*d_j^2, "
                        + "E^+_j has coefficient 125*d_j^2, and U^-_j,U^+_j replace d_j by B_j. "
                        + "The four points of infinite order are respectively "
                        + "(d_j*c_j,d_j*L_(3^j)), (5*d_j*c_j,25*d_j*F_(3^j)), "
                        + "(B_j,B_j*L_(3^j)), and (5*B_j,25*B_j*F_(3^j)).")),
                    Paragraph(Text(
                        "For distinct positive i,j, no rational q satisfies d_i=q^3*d_j. "
                        + "For either sign, no rational q has the corresponding coefficient "
                        + "ratio equal to q^6. These are literal conjuncts of the Lean theorem.")),
                    Paragraph(Text(
                        "The Lucas and Fibonacci identities and B_j=d_j*c_j^3 establish the "
                        + "point equations. Odd abscissas and nonzero even ordinates give a "
                        + "binary-unit X coordinate and positive Y valuation. The two-adic Mordell "
                        + "criterion makes the first double's X valuation negative; its valuation "
                        + "then strictly decreases along successive doubles, proving infinite order. "
                        + "Disjoint block prime supports, noncubicity, and factorization-based "
                        + "cube removal separate the twist parameters. Nonzero coefficients "
                        + "make every displayed model globally nonsingular.")),
                    Paragraph(Text(
                        "No Wall--Sun--Sun hypothesis is used. Infinite order does not show "
                        + "that any point lies outside a cubic-isogeny image; that is a "
                        + "separate claim."))),
                DescribeRole.Theorem))));

    private static Formula Sub(string symbol, string index) =>
        new Formula.Subscript(F.Id(symbol), F.Id(index));

    private static Formula Sub(string symbol, Formula index) =>
        new Formula.Subscript(F.Id(symbol), index);

    private static Formula TheoremFormula()
    {
        Formula j = F.Id("j");
        Formula i = F.Id("i");
        Formula dj = Sub("d", "j");
        Formula di = Sub("d", "i");
        Formula eminusJ = new Formula.Power(Sub("E", "j"), Minus);
        Formula eplusJ = new Formula.Power(Sub("E", "j"), Plus);
        Formula uminusJ = new Formula.Power(Sub("U", "j"), Minus);
        Formula uplusJ = new Formula.Power(Sub("U", "j"), Plus);
        Formula sminusJ = new Formula.Power(Sub("S", "j"), Minus);
        Formula splusJ = new Formula.Power(Sub("S", "j"), Plus);
        Formula tminusJ = new Formula.Power(Sub("T", "j"), Minus);
        Formula tplusJ = new Formula.Power(Sub("T", "j"), Plus);
        Formula noncube = NoRationalPower(di, dj, 3);
        Formula minusSixth = NoRationalPower(
            Seq(Minus, D(3), new Formula.Power(di, D(2))),
            Seq(Minus, D(3), new Formula.Power(dj, D(2))), 6);
        Formula plusSixth = NoRationalPower(
            Seq(D(1, 2, 5), new Formula.Power(di, D(2))),
            Seq(D(1, 2, 5), new Formula.Power(dj, D(2))), 6);
        return Disp(Seq(
            Forall, Sp, j, InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(1), Sp, Le, Sp, j, Sp, Rightarrow, Sp,
            Call("IsElliptic", eminusJ), Sp, Land, Sp,
            Call("IsElliptic", eplusJ), Sp, Land, Sp,
            Call("IsElliptic", uminusJ), Sp, Land, Sp,
            Call("IsElliptic", uplusJ), Comma, RowBreak, Grp(),
            Call("InfiniteOrder", sminusJ), Sp, Land, Sp,
            Call("InfiniteOrder", splusJ), Sp, Land, Sp,
            Call("InfiniteOrder", tminusJ), Sp, Land, Sp,
            Call("InfiniteOrder", tplusJ), Comma, RowBreak, Grp(),
            Forall, Sp, i, InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(1), Sp, Le, Sp, i, Sp, Land, Sp, i, Sp, Neq, Sp, j,
            Sp, Rightarrow, Sp, noncube, Sp, Land, Sp,
            minusSixth, Sp, Land, Sp, plusSixth));
    }

    private static Formula NoRationalPower(Formula numerator, Formula denominator, int exponent) =>
        new Formula.Not(Seq(
            Exists, Sp, F.Id("q"), InMacro, Mathbb, Grp(F.Id("Q")), Comma, Sp,
            new Formula.Fraction(numerator, denominator), Sp, Eq, Sp,
            new Formula.Power(F.Id("q"), D((byte)exponent))));
}
